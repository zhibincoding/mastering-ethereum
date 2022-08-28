// * 1.第一步首先要导入写好的gadget -> 一个是mod，一个是mod内的gadget

use super::util::{CachedRegion, CellManager, StoredExpression};
use crate::{
    evm_circuit::{
        param::{MAX_STEP_HEIGHT, STEP_WIDTH},
        step::{ExecutionState, Step},
        table::Table,
        util::{
            constraint_builder::{BaseConstraintBuilder, ConstraintBuilder},
            rlc, CellType,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::LookupTable,
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};
use std::{collections::HashMap, convert::TryInto, iter};
use strum::IntoEnumIterator;

mod add_sub;
mod addmod;
mod begin_tx;
mod bitwise;
mod block_ctx;
mod byte;
mod call;
mod calldatacopy;
mod calldataload;
mod calldatasize;
mod caller;
mod callvalue;
mod chainid;
mod codecopy;
mod codesize;
mod comparator;
mod dummy;
mod dup;
mod end_block;
mod end_tx;
mod error_oog_static_memory;
mod extcodehash;
mod gas;
mod gasprice;
mod is_zero;
mod jump;
mod jumpdest;
mod jumpi;
mod logs;
mod memory;
mod msize;
mod mul_div_mod;
mod mulmod;
mod not;
mod origin;
mod pc;
mod pop;
mod push;
mod r#return;
mod sdiv_smod;
mod selfbalance;
// ! 把SHL和SHR放到一起实现了
// * 这里是execution文件夹里面实现的gadget -> 主要是为了把这个库导入进去
// * 这里我们导入了shl_shr这个gadget，里面是各种constraint（需要理解一些halo2里面gadget这个概念）
mod shl_shr;
mod signed_comparator;
mod signextend;
mod sload;
mod sstore;
mod stop;
mod swap;

use add_sub::AddSubGadget;
use addmod::AddModGadget;
use begin_tx::BeginTxGadget;
use bitwise::BitwiseGadget;
use block_ctx::{BlockCtxU160Gadget, BlockCtxU256Gadget, BlockCtxU64Gadget};
use byte::ByteGadget;
use call::CallGadget;
use calldatacopy::CallDataCopyGadget;
use calldataload::CallDataLoadGadget;
use calldatasize::CallDataSizeGadget;
use caller::CallerGadget;
use callvalue::CallValueGadget;
use chainid::ChainIdGadget;
use codecopy::CodeCopyGadget;
use codesize::CodesizeGadget;
use comparator::ComparatorGadget;
use dummy::DummyGadget;
use dup::DupGadget;
use end_block::EndBlockGadget;
use end_tx::EndTxGadget;
use error_oog_static_memory::ErrorOOGStaticMemoryGadget;
use extcodehash::ExtcodehashGadget;
use gas::GasGadget;
use gasprice::GasPriceGadget;
use is_zero::IsZeroGadget;
use jump::JumpGadget;
use jumpdest::JumpdestGadget;
use jumpi::JumpiGadget;
use logs::LogGadget;
use memory::MemoryGadget;
use msize::MsizeGadget;
use mul_div_mod::MulDivModGadget;
use mulmod::MulModGadget;
use not::NotGadget;
use origin::OriginGadget;
use pc::PcGadget;
use pop::PopGadget;
use push::PushGadget;
use r#return::ReturnGadget;
use sdiv_smod::SignedDivModGadget;
use selfbalance::SelfbalanceGadget;
// ! before: use shr::ShrGadget
// ! 实现了一个`shl`和`shr`可以共用的gadget
// * 从shl_shr module中导入gadget
// * 可以研究一下gadget调用的Chip是哪个
use shl_shr::ShlShrGadget;
use signed_comparator::SignedComparatorGadget;
use signextend::SignextendGadget;
use sload::SloadGadget;
use sstore::SstoreGadget;
use stop::StopGadget;
use swap::SwapGadget;

pub(crate) trait ExecutionGadget<F: FieldExt> {
    const NAME: &'static str;

    const EXECUTION_STATE: ExecutionState;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self;

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error>;
}

// ! 跟Fibonacci一样 -> 首先实现一个config struct，然后实现对应的Chip，然后用gadget实现对应的电路
// * Execution config struct -> 这里应该是后面`EVM circuit`验证witness过程中会用到的gadgets
#[derive(Clone, Debug)]
pub(crate) struct ExecutionConfig<F> {
    q_usable: Selector,
    q_step: Column<Advice>,
    num_rows_until_next_step: Column<Advice>,
    num_rows_inv: Column<Advice>,
    q_step_first: Selector,
    q_step_last: Selector,
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    height_map: HashMap<ExecutionState, usize>,
    stored_expressions_map: HashMap<ExecutionState, Vec<StoredExpression<F>>>,
    // internal state gadgets
    begin_tx_gadget: BeginTxGadget<F>,
    end_block_gadget: EndBlockGadget<F>,
    end_tx_gadget: EndTxGadget<F>,
    // opcode gadgets
    add_sub_gadget: AddSubGadget<F>,
    addmod_gadget: AddModGadget<F>,
    bitwise_gadget: BitwiseGadget<F>,
    byte_gadget: ByteGadget<F>,
    call_gadget: CallGadget<F>,
    call_value_gadget: CallValueGadget<F>,
    calldatacopy_gadget: CallDataCopyGadget<F>,
    calldataload_gadget: CallDataLoadGadget<F>,
    calldatasize_gadget: CallDataSizeGadget<F>,
    caller_gadget: CallerGadget<F>,
    chainid_gadget: ChainIdGadget<F>,
    codecopy_gadget: CodeCopyGadget<F>,
    codesize_gadget: CodesizeGadget<F>,
    comparator_gadget: ComparatorGadget<F>,
    dup_gadget: DupGadget<F>,
    extcodehash_gadget: ExtcodehashGadget<F>,
    gas_gadget: GasGadget<F>,
    gasprice_gadget: GasPriceGadget<F>,
    iszero_gadget: IsZeroGadget<F>,
    jump_gadget: JumpGadget<F>,
    jumpdest_gadget: JumpdestGadget<F>,
    jumpi_gadget: JumpiGadget<F>,
    log_gadget: LogGadget<F>,
    memory_gadget: MemoryGadget<F>,
    msize_gadget: MsizeGadget<F>,
    mul_div_mod_gadget: MulDivModGadget<F>,
    mulmod_gadget: MulModGadget<F>,
    not_gadget: NotGadget<F>,
    origin_gadget: OriginGadget<F>,
    pc_gadget: PcGadget<F>,
    pop_gadget: PopGadget<F>,
    push_gadget: PushGadget<F>,
    return_gadget: ReturnGadget<F>,
    sdiv_smod_gadget: SignedDivModGadget<F>,
    selfbalance_gadget: SelfbalanceGadget<F>,
    sha3_gadget: DummyGadget<F, 2, 1, { ExecutionState::SHA3 }>,
    address_gadget: DummyGadget<F, 0, 1, { ExecutionState::ADDRESS }>,
    balance_gadget: DummyGadget<F, 1, 1, { ExecutionState::BALANCE }>,
    blockhash_gadget: DummyGadget<F, 1, 1, { ExecutionState::BLOCKHASH }>,
    exp_gadget: DummyGadget<F, 2, 1, { ExecutionState::EXP }>,
    sar_gadget: DummyGadget<F, 2, 1, { ExecutionState::SAR }>,
    extcodesize_gadget: DummyGadget<F, 1, 1, { ExecutionState::EXTCODESIZE }>,
    extcodecopy_gadget: DummyGadget<F, 4, 0, { ExecutionState::EXTCODECOPY }>,
    returndatasize_gadget: DummyGadget<F, 0, 1, { ExecutionState::RETURNDATASIZE }>,
    returndatacopy_gadget: DummyGadget<F, 3, 0, { ExecutionState::RETURNDATACOPY }>,
    create_gadget: DummyGadget<F, 3, 1, { ExecutionState::CREATE }>,
    callcode_gadget: DummyGadget<F, 7, 1, { ExecutionState::CALLCODE }>,
    delegatecall_gadget: DummyGadget<F, 6, 1, { ExecutionState::DELEGATECALL }>,
    create2_gadget: DummyGadget<F, 4, 1, { ExecutionState::CREATE2 }>,
    staticcall_gadget: DummyGadget<F, 6, 1, { ExecutionState::STATICCALL }>,
    selfdestruct_gadget: DummyGadget<F, 1, 0, { ExecutionState::SELFDESTRUCT }>,
    // ! 之前有两个单独的gadget，分别是shl和shr
    // ! 现在这两个单独的gadget被合二为一了
    // * 导入的全是gadget

    // * 正常的circuit里这里都是一堆columns的config
    // * 不过这里是整个EVM circuit执行文件的config，所以配置的全都是gadgets
    shl_shr_gadget: ShlShrGadget<F>,
    signed_comparator_gadget: SignedComparatorGadget<F>,
    signextend_gadget: SignextendGadget<F>,
    sload_gadget: SloadGadget<F>,
    sstore_gadget: SstoreGadget<F>,
    stop_gadget: StopGadget<F>,
    swap_gadget: SwapGadget<F>,
    block_ctx_u64_gadget: BlockCtxU64Gadget<F>,
    block_ctx_u160_gadget: BlockCtxU160Gadget<F>,
    block_ctx_u256_gadget: BlockCtxU256Gadget<F>,
    // error gadgets
    error_oog_static_memory_gadget: ErrorOOGStaticMemoryGadget<F>,
}

// ! `shl`分别在`configure`和`assign_exec_step_int`函数里
impl<F: Field> ExecutionConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn configure(
        // * 这里其实就像一个Fibonacci的Chip一样，因为有ConstranitSystem存在
        // * 这里的meta可以用来`create columns`和`define custom gates`
        // * 我们可以看看在这里主要用来做什么
        meta: &mut ConstraintSystem<F>,
        // * 这个不清楚是什么
        power_of_randomness: [Expression<F>; 31],
        // * 用到的tables
        // * fixed、byte、tx、rw、bytecode、block、copy
        fixed_table: &dyn LookupTable<F>,
        byte_table: &dyn LookupTable<F>,
        tx_table: &dyn LookupTable<F>,
        rw_table: &dyn LookupTable<F>,
        bytecode_table: &dyn LookupTable<F>,
        block_table: &dyn LookupTable<F>,
        copy_table: &dyn LookupTable<F>,
    ) -> Self {
        // * 定义各种columns
        // * 在这里主要就是advice column和selector
        let q_usable = meta.complex_selector();
        let q_step = meta.advice_column();
        let num_rows_until_next_step = meta.advice_column();
        let num_rows_inv = meta.advice_column();
        let q_step_first = meta.complex_selector();
        let q_step_last = meta.complex_selector();
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());

        let step_curr = Step::new(meta, advices, 0);
        let mut height_map = HashMap::new();

        // * 主要写了两个gate -> 分别是约束execution state、和q_step
        // * 从这里就可以感受出evm circuit(zkevm)最早的设计思想
        meta.create_gate("Constrain execution state", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let q_step_first = meta.query_selector(q_step_first);
            let q_step_last = meta.query_selector(q_step_last);

            // Only one of execution_state should be enabled
            let sum_to_one = (
                "Only one of execution_state should be enabled",
                step_curr
                    .state
                    .execution_state
                    .iter()
                    .fold(1u64.expr(), |acc, cell| acc - cell.expr()),
            );

            // Cells representation for execution_state should be bool.
            let bool_checks = step_curr.state.execution_state.iter().map(|cell| {
                (
                    "Representation for execution_state should be bool",
                    cell.expr() * (1u64.expr() - cell.expr()),
                )
            });

            let _first_step_check = {
                let begin_tx_selector =
                    step_curr.execution_state_selector([ExecutionState::BeginTx]);
                iter::once((
                    "First step should be BeginTx",
                    q_step_first * (1.expr() - begin_tx_selector),
                ))
            };

            let _last_step_check = {
                let end_block_selector =
                    step_curr.execution_state_selector([ExecutionState::EndBlock]);
                iter::once((
                    "Last step should be EndBlock",
                    q_step_last * (1.expr() - end_block_selector),
                ))
            };

            iter::once(sum_to_one)
                .chain(bool_checks)
                .map(move |(name, poly)| (name, q_usable.clone() * q_step.clone() * poly))
            // TODO: Enable these after incomplete trace is no longer necessary.
            // .chain(first_step_check)
            // .chain(last_step_check)
        });

        meta.create_gate("q_step", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step_first = meta.query_selector(q_step_first);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let num_rows_left_cur = meta.query_advice(num_rows_until_next_step, Rotation::cur());
            let num_rows_left_next = meta.query_advice(num_rows_until_next_step, Rotation::next());
            let num_rows_left_inverse = meta.query_advice(num_rows_inv, Rotation::cur());

            let mut cb = BaseConstraintBuilder::default();
            // q_step needs to be enabled on the first row
            cb.condition(q_step_first, |cb| {
                cb.require_equal("q_step == 1", q_step.clone(), 1.expr());
            });
            // Except when step is enabled, the step counter needs to decrease by 1
            cb.condition(1.expr() - q_step.clone(), |cb| {
                cb.require_equal(
                    "num_rows_left_cur := num_rows_left_next + 1",
                    num_rows_left_cur.clone(),
                    num_rows_left_next + 1.expr(),
                );
            });
            // Enforce that q_step := num_rows_until_next_step == 0
            let is_zero = 1.expr() - (num_rows_left_cur.clone() * num_rows_left_inverse.clone());
            cb.require_zero(
                "num_rows_left_cur * is_zero == 0",
                num_rows_left_cur * is_zero.clone(),
            );
            cb.require_zero(
                "num_rows_left_inverse * is_zero == 0",
                num_rows_left_inverse * is_zero.clone(),
            );
            cb.require_equal("q_step == is_zero", q_step, is_zero);
            // On each usable row
            cb.gate(q_usable)
        });

        let mut stored_expressions_map = HashMap::new();
        let step_next = Step::new(meta, advices, MAX_STEP_HEIGHT);
        macro_rules! configure_gadget {
            () => {
                Self::configure_gadget(
                    meta,
                    advices,
                    q_usable,
                    q_step,
                    num_rows_until_next_step,
                    q_step_first,
                    q_step_last,
                    &power_of_randomness,
                    &step_curr,
                    &step_next,
                    &mut height_map,
                    &mut stored_expressions_map,
                )
            };
        }

        let cell_manager = step_curr.cell_manager.clone();
        let config = Self {
            q_usable,
            q_step,
            num_rows_until_next_step,
            num_rows_inv,
            q_step_first,
            q_step_last,
            advices,
            // internal states
            begin_tx_gadget: configure_gadget!(),
            end_block_gadget: configure_gadget!(),
            end_tx_gadget: configure_gadget!(),
            // opcode gadgets
            add_sub_gadget: configure_gadget!(),
            addmod_gadget: configure_gadget!(),
            bitwise_gadget: configure_gadget!(),
            byte_gadget: configure_gadget!(),
            call_gadget: configure_gadget!(),
            call_value_gadget: configure_gadget!(),
            calldatacopy_gadget: configure_gadget!(),
            calldataload_gadget: configure_gadget!(),
            calldatasize_gadget: configure_gadget!(),
            caller_gadget: configure_gadget!(),
            chainid_gadget: configure_gadget!(),
            codecopy_gadget: configure_gadget!(),
            codesize_gadget: configure_gadget!(),
            comparator_gadget: configure_gadget!(),
            dup_gadget: configure_gadget!(),
            extcodehash_gadget: configure_gadget!(),
            gas_gadget: configure_gadget!(),
            gasprice_gadget: configure_gadget!(),
            iszero_gadget: configure_gadget!(),
            jump_gadget: configure_gadget!(),
            jumpdest_gadget: configure_gadget!(),
            jumpi_gadget: configure_gadget!(),
            log_gadget: configure_gadget!(),
            memory_gadget: configure_gadget!(),
            msize_gadget: configure_gadget!(),
            mul_div_mod_gadget: configure_gadget!(),
            mulmod_gadget: configure_gadget!(),
            not_gadget: configure_gadget!(),
            origin_gadget: configure_gadget!(),
            pc_gadget: configure_gadget!(),
            pop_gadget: configure_gadget!(),
            push_gadget: configure_gadget!(),
            return_gadget: configure_gadget!(),
            sdiv_smod_gadget: configure_gadget!(),
            selfbalance_gadget: configure_gadget!(),
            sha3_gadget: configure_gadget!(),
            address_gadget: configure_gadget!(),
            balance_gadget: configure_gadget!(),
            blockhash_gadget: configure_gadget!(),
            exp_gadget: configure_gadget!(),
            sar_gadget: configure_gadget!(),
            extcodesize_gadget: configure_gadget!(),
            extcodecopy_gadget: configure_gadget!(),
            returndatasize_gadget: configure_gadget!(),
            returndatacopy_gadget: configure_gadget!(),
            create_gadget: configure_gadget!(),
            callcode_gadget: configure_gadget!(),
            delegatecall_gadget: configure_gadget!(),
            create2_gadget: configure_gadget!(),
            staticcall_gadget: configure_gadget!(),
            selfdestruct_gadget: configure_gadget!(),
            // ! 这里是configure的部分，类似于assign和register，注册一个新的opcode和gadget
            shl_shr_gadget: configure_gadget!(),
            signed_comparator_gadget: configure_gadget!(),
            signextend_gadget: configure_gadget!(),
            sload_gadget: configure_gadget!(),
            sstore_gadget: configure_gadget!(),
            stop_gadget: configure_gadget!(),
            swap_gadget: configure_gadget!(),
            block_ctx_u64_gadget: configure_gadget!(),
            block_ctx_u160_gadget: configure_gadget!(),
            block_ctx_u256_gadget: configure_gadget!(),
            // error gadgets
            error_oog_static_memory_gadget: configure_gadget!(),
            // step and presets
            step: step_curr,
            height_map,
            stored_expressions_map,
        };

        Self::configure_lookup(
            meta,
            fixed_table,
            byte_table,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            &power_of_randomness,
            &cell_manager,
        );

        config
    }

    pub fn get_step_height_option(&self, execution_state: ExecutionState) -> Option<usize> {
        self.height_map.get(&execution_state).copied()
    }

    pub fn get_step_height(&self, execution_state: ExecutionState) -> usize {
        self.get_step_height_option(execution_state)
            .unwrap_or_else(|| panic!("Execution state unknown: {:?}", execution_state))
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_gadget<G: ExecutionGadget<F>>(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; STEP_WIDTH],
        q_usable: Selector,
        q_step: Column<Advice>,
        num_rows_until_next_step: Column<Advice>,
        q_step_first: Selector,
        q_step_last: Selector,
        power_of_randomness: &[Expression<F>; 31],
        step_curr: &Step<F>,
        step_next: &Step<F>,
        height_map: &mut HashMap<ExecutionState, usize>,
        stored_expressions_map: &mut HashMap<ExecutionState, Vec<StoredExpression<F>>>,
    ) -> G {
        // Configure the gadget with the max height first so we can find out the actual
        // height
        let height = {
            let mut cb = ConstraintBuilder::new(
                step_curr.clone(),
                step_next.clone(),
                power_of_randomness,
                G::EXECUTION_STATE,
            );
            G::configure(&mut cb);
            let (_, _, _, height) = cb.build();
            height
        };

        // Now actually configure the gadget with the correct minimal height
        let step_next = &Step::new(meta, advices, height);
        let mut cb = ConstraintBuilder::new(
            step_curr.clone(),
            step_next.clone(),
            power_of_randomness,
            G::EXECUTION_STATE,
        );

        let gadget = G::configure(&mut cb);

        // Enforce the step height for this opcode
        // * 这是额外的两个gate -> 分别是`query num rows`和`约束state machine的transition`
        let mut num_rows_until_next_step_next = 0.expr();
        meta.create_gate("query num rows", |meta| {
            num_rows_until_next_step_next =
                meta.query_advice(num_rows_until_next_step, Rotation::next());
            vec![0.expr()]
        });
        cb.require_equal(
            "num_rows_until_next_step_next := height - 1",
            num_rows_until_next_step_next,
            (height - 1).expr(),
        );

        let (constraints, constraints_first_step, stored_expressions, _) = cb.build();
        debug_assert!(
            !height_map.contains_key(&G::EXECUTION_STATE),
            "execution state already configured"
        );
        height_map.insert(G::EXECUTION_STATE, height);
        debug_assert!(
            !stored_expressions_map.contains_key(&G::EXECUTION_STATE),
            "execution state already configured"
        );
        stored_expressions_map.insert(G::EXECUTION_STATE, stored_expressions);

        // Enforce the logic for this opcode
        let q_steps: &dyn Fn(&mut VirtualCells<F>) -> Expression<F> =
            &|meta| meta.query_advice(q_step, Rotation::cur());
        let q_steps_first: &dyn Fn(&mut VirtualCells<F>) -> Expression<F> =
            &|meta| meta.query_selector(q_step_first);
        for (selector, constraints) in [
            (q_steps, constraints),
            (q_steps_first, constraints_first_step),
        ] {
            if !constraints.is_empty() {
                meta.create_gate(G::NAME, |meta| {
                    let q_usable = meta.query_selector(q_usable);
                    let selector = selector(meta);
                    constraints.into_iter().map(move |(name, constraint)| {
                        (name, q_usable.clone() * selector.clone() * constraint)
                    })
                });
            }
        }

        // Enforce the state transitions for this opcode
        meta.create_gate("Constrain state machine transitions", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let q_step_last = meta.query_selector(q_step_last);

            // ExecutionState transition should be correct.
            iter::empty()
                .chain(
                    IntoIterator::into_iter([
                        (
                            "EndTx can only transit to BeginTx or EndBlock",
                            ExecutionState::EndTx,
                            vec![ExecutionState::BeginTx, ExecutionState::EndBlock],
                        ),
                        (
                            "EndBlock can only transit to EndBlock",
                            ExecutionState::EndBlock,
                            vec![ExecutionState::EndBlock],
                        ),
                    ])
                    .filter(move |(_, from, _)| *from == G::EXECUTION_STATE)
                    .map(|(_, _, to)| 1.expr() - step_next.execution_state_selector(to)),
                )
                .chain(
                    IntoIterator::into_iter([
                        (
                            "Only EndTx can transit to BeginTx",
                            ExecutionState::BeginTx,
                            vec![ExecutionState::EndTx],
                        ),
                        (
                            "Only ExecutionState which halts or BeginTx can transit to EndTx",
                            ExecutionState::EndTx,
                            ExecutionState::iter()
                                .filter(ExecutionState::halts)
                                .chain(iter::once(ExecutionState::BeginTx))
                                .collect(),
                        ),
                        (
                            "Only EndTx or EndBlock can transit to EndBlock",
                            ExecutionState::EndBlock,
                            vec![ExecutionState::EndTx, ExecutionState::EndBlock],
                        ),
                    ])
                    .filter(move |(_, _, from)| !from.contains(&G::EXECUTION_STATE))
                    .map(|(_, to, _)| step_next.execution_state_selector([to])),
                )
                // Accumulate all state transition checks.
                // This can be done because all summed values are enforced to be boolean.
                .reduce(|accum, poly| accum + poly)
                .map(move |poly| {
                    q_usable.clone()
                        * q_step.clone()
                        * (1.expr() - q_step_last.clone())
                        * step_curr.execution_state_selector([G::EXECUTION_STATE])
                        * poly
                })
        });

        gadget
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_lookup(
        meta: &mut ConstraintSystem<F>,
        fixed_table: &dyn LookupTable<F>,
        byte_table: &dyn LookupTable<F>,
        tx_table: &dyn LookupTable<F>,
        rw_table: &dyn LookupTable<F>,
        bytecode_table: &dyn LookupTable<F>,
        block_table: &dyn LookupTable<F>,
        copy_table: &dyn LookupTable<F>,
        power_of_randomness: &[Expression<F>; 31],
        cell_manager: &CellManager<F>,
    ) {
        for column in cell_manager.columns().iter() {
            if let CellType::Lookup(table) = column.cell_type {
                let name = format!("{:?}", table);
                meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                    let table_expressions = match table {
                        Table::Fixed => fixed_table,
                        Table::Tx => tx_table,
                        Table::Rw => rw_table,
                        Table::Bytecode => bytecode_table,
                        Table::Block => block_table,
                        Table::Byte => byte_table,
                        Table::Copy => copy_table,
                    }
                    .table_exprs(meta);
                    vec![(
                        column.expr(),
                        rlc::expr(&table_expressions, power_of_randomness),
                    )]
                });
            }
        }
    }

    /// Assign block
    /// When exact is enabled, assign exact steps in block without padding for
    /// unit test purpose
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
        _exact: bool,
    ) -> Result<(), Error> {
        let power_of_randomness = (1..32)
            .map(|exp| block.randomness.pow(&[exp, 0, 0, 0]))
            .collect::<Vec<F>>()
            .try_into()
            .unwrap();

        layouter.assign_region(
            || "Execution step",
            |mut region| {
                let mut offset = 0;

                self.q_step_first.enable(&mut region, offset)?;

                // Collect all steps
                let mut steps = block
                    .txs
                    .iter()
                    .flat_map(|tx| tx.steps.iter().map(move |step| (tx, step)))
                    .peekable();

                let mut last_height = 0;
                while let Some((transaction, step)) = steps.next() {
                    let call = &transaction.calls[step.call_index];
                    let height = self.get_step_height(step.execution_state);

                    // Assign the step witness
                    self.assign_exec_step(
                        &mut region,
                        offset,
                        block,
                        transaction,
                        call,
                        step,
                        height,
                        steps.peek().map(|&(transaction, step)| {
                            (transaction, &transaction.calls[step.call_index], step)
                        }),
                        power_of_randomness,
                    )?;

                    // q_step logic
                    for idx in 0..height {
                        let offset = offset + idx;
                        self.q_usable.enable(&mut region, offset)?;
                        region.assign_advice(
                            || "step selector",
                            self.q_step,
                            offset,
                            || Ok(if idx == 0 { F::one() } else { F::zero() }),
                        )?;
                        let value = if idx == 0 {
                            F::zero()
                        } else {
                            F::from((height - idx) as u64)
                        };
                        region.assign_advice(
                            || "step height",
                            self.num_rows_until_next_step,
                            offset,
                            || Ok(value),
                        )?;
                        region.assign_advice(
                            || "step height inv",
                            self.num_rows_inv,
                            offset,
                            || Ok(value.invert().unwrap_or(F::zero())),
                        )?;
                    }

                    offset += height;
                    last_height = height;
                }
                // These are still referenced (but not used) in next rows
                region.assign_advice(
                    || "step height",
                    self.num_rows_until_next_step,
                    offset,
                    || Ok(F::zero()),
                )?;
                region.assign_advice(
                    || "step height inv",
                    self.q_step,
                    offset,
                    || Ok(F::zero()),
                )?;

                // If not exact:
                // TODO: Pad leftover region to the desired capacity
                // TODO: Enable q_step_last
                self.q_step_last.enable(&mut region, offset - last_height)?;

                Ok(())
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
        height: usize,
        next: Option<(&Transaction, &Call, &ExecStep)>,
        power_of_randomness: [F; 31],
    ) -> Result<(), Error> {
        // Make the region large enough for the current step and the next step.
        // The next step's next step may also be accessed, so make the region large
        // enough for 3 steps.
        let region = &mut CachedRegion::<'_, '_, F>::new(
            region,
            power_of_randomness,
            STEP_WIDTH,
            MAX_STEP_HEIGHT * 3,
            self.advices[0].index(),
            offset,
        );

        // Also set the witness of the next step.
        // These may be used in stored expressions and
        // so their witness values need to be known to be able
        // to correctly calculate the intermediate value.
        if let Some((transaction_next, call_next, step_next)) = next {
            self.assign_exec_step_int(
                region,
                offset + height,
                block,
                transaction_next,
                call_next,
                step_next,
            )?;
        }

        self.assign_exec_step_int(region, offset, block, transaction, call, step)
    }

    fn assign_exec_step_int(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        log::trace!("assign_exec_step offset:{} step:{:?}", offset, step);
        self.step
            .assign_exec_step(region, offset, block, transaction, call, step)?;

        macro_rules! assign_exec_step {
            ($gadget:expr) => {
                // * 貌似是每个gadget里面的参数
                $gadget.assign_exec_step(region, offset, block, transaction, call, step)?
            };
        }

        // * 这里会匹配execution里面对应的操作 -> 也就是execution state
        // * 匹配到对应的操作以后，会match到对应的gadget，从而做约束
        match step.execution_state {
            // internal states
            // * 初始状态 -> BeginTx
            // * 为啥EndTx和EndBlock也放到最前面
            ExecutionState::BeginTx => assign_exec_step!(self.begin_tx_gadget),
            ExecutionState::EndTx => assign_exec_step!(self.end_tx_gadget),
            ExecutionState::EndBlock => assign_exec_step!(self.end_block_gadget),
            // opcode
            // * 这里是每一个opcode
            ExecutionState::ADD_SUB => assign_exec_step!(self.add_sub_gadget),
            ExecutionState::ADDMOD => assign_exec_step!(self.addmod_gadget),
            ExecutionState::BITWISE => assign_exec_step!(self.bitwise_gadget),
            ExecutionState::BYTE => assign_exec_step!(self.byte_gadget),
            ExecutionState::CALL => assign_exec_step!(self.call_gadget),
            ExecutionState::CALLDATACOPY => assign_exec_step!(self.calldatacopy_gadget),
            ExecutionState::CALLDATALOAD => assign_exec_step!(self.calldataload_gadget),
            ExecutionState::CALLDATASIZE => assign_exec_step!(self.calldatasize_gadget),
            ExecutionState::CALLER => assign_exec_step!(self.caller_gadget),
            ExecutionState::CALLVALUE => assign_exec_step!(self.call_value_gadget),
            ExecutionState::CHAINID => assign_exec_step!(self.chainid_gadget),
            ExecutionState::CODECOPY => assign_exec_step!(self.codecopy_gadget),
            ExecutionState::CODESIZE => assign_exec_step!(self.codesize_gadget),
            ExecutionState::CMP => assign_exec_step!(self.comparator_gadget),
            ExecutionState::DUP => assign_exec_step!(self.dup_gadget),
            ExecutionState::EXTCODEHASH => assign_exec_step!(self.extcodehash_gadget),
            ExecutionState::GAS => assign_exec_step!(self.gas_gadget),
            ExecutionState::GASPRICE => assign_exec_step!(self.gasprice_gadget),
            ExecutionState::ISZERO => assign_exec_step!(self.iszero_gadget),
            ExecutionState::JUMP => assign_exec_step!(self.jump_gadget),
            ExecutionState::JUMPDEST => assign_exec_step!(self.jumpdest_gadget),
            ExecutionState::JUMPI => assign_exec_step!(self.jumpi_gadget),
            ExecutionState::LOG => assign_exec_step!(self.log_gadget),
            ExecutionState::MEMORY => assign_exec_step!(self.memory_gadget),
            ExecutionState::MSIZE => assign_exec_step!(self.msize_gadget),
            ExecutionState::MUL_DIV_MOD => assign_exec_step!(self.mul_div_mod_gadget),
            ExecutionState::MULMOD => assign_exec_step!(self.mulmod_gadget),
            ExecutionState::NOT => assign_exec_step!(self.not_gadget),
            ExecutionState::ORIGIN => assign_exec_step!(self.origin_gadget),
            ExecutionState::PC => assign_exec_step!(self.pc_gadget),
            ExecutionState::POP => assign_exec_step!(self.pop_gadget),
            ExecutionState::PUSH => assign_exec_step!(self.push_gadget),
            ExecutionState::RETURN => assign_exec_step!(self.return_gadget),
            ExecutionState::SCMP => assign_exec_step!(self.signed_comparator_gadget),
            ExecutionState::SDIV_SMOD => assign_exec_step!(self.sdiv_smod_gadget),
            ExecutionState::BLOCKCTXU64 => assign_exec_step!(self.block_ctx_u64_gadget),
            ExecutionState::BLOCKCTXU160 => assign_exec_step!(self.block_ctx_u160_gadget),
            ExecutionState::BLOCKCTXU256 => assign_exec_step!(self.block_ctx_u256_gadget),
            ExecutionState::SELFBALANCE => assign_exec_step!(self.selfbalance_gadget),
            // dummy gadgets
            // * 这部分是某个叫dummy的东西，并不是真实的opcode
            // * 这些opcode还需要时间慢慢实现，比如SHA3、BALANCE等
            ExecutionState::SHA3 => assign_exec_step!(self.sha3_gadget),
            ExecutionState::ADDRESS => assign_exec_step!(self.address_gadget),
            ExecutionState::BALANCE => assign_exec_step!(self.balance_gadget),
            ExecutionState::BLOCKHASH => assign_exec_step!(self.blockhash_gadget),
            ExecutionState::EXP => assign_exec_step!(self.exp_gadget),
            ExecutionState::SAR => assign_exec_step!(self.sar_gadget),
            ExecutionState::EXTCODESIZE => assign_exec_step!(self.extcodesize_gadget),
            ExecutionState::EXTCODECOPY => assign_exec_step!(self.extcodecopy_gadget),
            ExecutionState::RETURNDATASIZE => assign_exec_step!(self.returndatasize_gadget),
            ExecutionState::RETURNDATACOPY => assign_exec_step!(self.returndatacopy_gadget),
            ExecutionState::CREATE => assign_exec_step!(self.create_gadget),
            ExecutionState::CALLCODE => assign_exec_step!(self.callcode_gadget),
            ExecutionState::DELEGATECALL => assign_exec_step!(self.delegatecall_gadget),
            ExecutionState::CREATE2 => assign_exec_step!(self.create2_gadget),
            ExecutionState::STATICCALL => assign_exec_step!(self.staticcall_gadget),
            ExecutionState::SELFDESTRUCT => assign_exec_step!(self.selfdestruct_gadget),
            // end of dummy gadgets
            // ! 我们添加到SHL opcode
            // * 这部分如果实现了，感觉可以放到dummy gadget之前
            ExecutionState::SHL_SHR => assign_exec_step!(self.shl_shr_gadget),
            ExecutionState::SIGNEXTEND => assign_exec_step!(self.signextend_gadget),
            ExecutionState::SLOAD => assign_exec_step!(self.sload_gadget),
            ExecutionState::SSTORE => assign_exec_step!(self.sstore_gadget),
            ExecutionState::STOP => assign_exec_step!(self.stop_gadget),
            ExecutionState::SWAP => assign_exec_step!(self.swap_gadget),
            // errors
            // * 这里应该会实现几乎所有的error case
            // * 总体来说就是OOG和non-OOG
            ExecutionState::ErrorOutOfGasStaticMemoryExpansion => {
                assign_exec_step!(self.error_oog_static_memory_gadget)
            }
            _ => unimplemented!("unimplemented ExecutionState: {:?}", step.execution_state),
        }

        // Fill in the witness values for stored expressions
        for stored_expression in self
            .stored_expressions_map
            .get(&step.execution_state)
            .unwrap_or_else(|| panic!("Execution state unknown: {:?}", step.execution_state))
        {
            stored_expression.assign(region, offset)?;
        }

        Ok(())
    }
}