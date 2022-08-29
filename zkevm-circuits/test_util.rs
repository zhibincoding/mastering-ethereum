use crate::{evm_circuit::witness::Block, state_circuit::StateCircuit};
use bus_mapping::mock::BlockData;
use eth_types::geth_types::{GethData, Transaction};
use ethers_core::types::{NameOrAddress, TransactionRequest};
use ethers_core::utils::keccak256;
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::dev::{MockProver, VerifyFailure};
use halo2_proofs::pairing::bn256::Fr;
use mock::TestContext;
use rand::{CryptoRng, Rng};

#[cfg(test)]
#[ctor::ctor]
fn init_env_logger() {
    // Enable RUST_LOG during tests
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error")).init();
}

#[derive(Debug, Clone)]
pub struct BytecodeTestConfig {
    pub enable_evm_circuit_test: bool,
    pub enable_state_circuit_test: bool,
    pub gas_limit: u64,
}

impl Default for BytecodeTestConfig {
    fn default() -> Self {
        Self {
            enable_evm_circuit_test: true,
            enable_state_circuit_test: true,
            gas_limit: 1_000_000u64,
        }
    }
}

// * `NACC`和`NTX`类似于范型，但是有具体的类型（usize），参考 https://www.runoob.com/rust/rust-generics.html
// * 范型是fn run_test_circuits<T>

// * 把NACC和NTX这两个东西传入给TestContext -> 都是usize类型（所以NACC和NTX的作用是什么，只是一个命名的作用吗）
// * 也就是说，抛开命名的效果，TestContext<NACC, NTX> = TestContext<usize, usize>
pub fn run_test_circuits<const NACC: usize, const NTX: usize>(
  // ! test_ctx中包含的信息量比较大 -> 比如chain Id、account list、history hashes（一个vector，存储最近256个blocks的hash）、geth里面跑出来的block、geth里面跑出来的trace
  // * 所以我猜跑测试的时候，我们传入了一个模拟的block和trace环境（提供了circuit用来证明所需要的上下文）
  test_ctx: TestContext<NACC, NTX>,
  // ! 这东西是一个Option<T> -> 也就是要不然返回Some<T>，要不然返回None（就是一个范型）
  // * 这里的T是`BytecodeTestConfig`，是一个struct类型，理解成跟上面一样的东西就行（一般我们跑测试的时候貌似这个参数是None）
  // * 这里传入的是一些config，比如是否开启evm circuit & state circuit的测试，还有配置的gas-limit等
  config: Option<BytecodeTestConfig>,
) -> Result<(), Vec<VerifyFailure>> {
  // * 初始化一些testContext数据 -> ChainId、HistoryHashes、Block data、Trace data、AccountList
  // * 这些数据也被称为GethData -> Block和Trace就是circuit input的主要内容
  let block: GethData = test_ctx.into();
  // ! 返回一个新的CircuitInputBuilder对象
  // * 1）new函数 -> 返回一个新的CircuitInputBuilder对象（sdb、codeDB、block）
  // *              传入一个完整的block数据，取出其中的内容，构造一个新的builder
  // * 2）new_from_geth_data函数 -> 通过geth返回block数据，生成一个新的block
  let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
  builder
      // * 这里貌似会把数据传进去处理一遍 -> 应该是通过Bus-Mapping把数据处理成我们需要的形式
      .handle_block(&block.eth_block, &block.geth_traces)
      .unwrap();

  // build a witness block from trace result
  // * 再把处理后的数据转换成witness形式
  let block = crate::evm_circuit::witness::block_convert(&builder.block, &builder.code_db);

  // finish required tests according to config using this witness block
  // * witness配合设置好的config，进行circuit test
  test_circuits_using_witness_block(block, config.unwrap_or_default())
}

pub fn test_circuits_using_witness_block(
    block: Block<Fr>,
    config: BytecodeTestConfig,
) -> Result<(), Vec<VerifyFailure>> {
    // run evm circuit test
    if config.enable_evm_circuit_test {
        crate::evm_circuit::test::run_test_circuit(block.clone())?;
    }

    // run state circuit test
    // TODO: use randomness as one of the circuit public input, since randomness in
    // state circuit and evm circuit must be same
    if config.enable_state_circuit_test {
        const N_ROWS: usize = 1 << 16;
        let state_circuit = StateCircuit::<Fr>::new(block.randomness, block.rws, N_ROWS);
        let power_of_randomness = state_circuit.instance();
        let prover = MockProver::<Fr>::run(18, &state_circuit, power_of_randomness).unwrap();
        prover.verify_at_rows(
            N_ROWS - state_circuit.rows.len()..N_ROWS,
            N_ROWS - state_circuit.rows.len()..N_ROWS,
        )?
    }

    Ok(())
}

pub fn rand_tx<R: Rng + CryptoRng>(mut rng: R, chain_id: u64) -> Transaction {
    let wallet0 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let wallet1 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
    let from = wallet0.address();
    let to = wallet1.address();
    let data = b"hello";
    let tx = TransactionRequest::new()
        .from(from)
        .to(to)
        .nonce(3)
        .value(1000)
        .data(data)
        .gas(500_000)
        .gas_price(1234);
    let tx_rlp = tx.rlp(chain_id);
    let sighash = keccak256(tx_rlp.as_ref()).into();
    let sig = wallet0.sign_hash(sighash, true);
    let to = tx.to.map(|to| match to {
        NameOrAddress::Address(a) => a,
        _ => unreachable!(),
    });
    Transaction {
        from: tx.from.unwrap(),
        to,
        gas_limit: tx.gas.unwrap(),
        gas_price: tx.gas_price.unwrap(),
        value: tx.value.unwrap(),
        call_data: tx.data.unwrap(),
        nonce: tx.nonce.unwrap(),
        v: sig.v,
        r: sig.r,
        s: sig.s,
        ..Transaction::default()
    }
}
