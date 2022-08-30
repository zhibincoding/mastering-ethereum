// ! 主要用于研究测试模块
use crate::{
  evm_circuit::{
      execution::ExecutionGadget,
      step::ExecutionState,
      util::{
          common_gadget::SameContextGadget,
          constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
          math_gadget::ShrWordsGadget,
          CachedRegion,
      },
      witness::{Block, Call, ExecStep, Transaction},
  },
  util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct ShrGadget<F> {
  same_context: SameContextGadget<F>,
  shr_words: ShrWordsGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ShrGadget<F> {
  const NAME: &'static str = "SHR";

  const EXECUTION_STATE: ExecutionState = ExecutionState::SHR;

  fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
      let opcode = cb.query_cell();

      let a = cb.query_word();
      let shift = cb.query_word();

      cb.stack_pop(shift.expr());
      cb.stack_pop(a.expr());
      let shr_words = ShrWordsGadget::construct(cb, a, shift);
      cb.stack_push(shr_words.b().expr());

      let step_state_transition = StepStateTransition {
          rw_counter: Delta(3.expr()),
          program_counter: Delta(1.expr()),
          stack_pointer: Delta(1.expr()),
          gas_left: Delta(-OpcodeId::SHR.constant_gas_cost().expr()),
          ..Default::default()
      };
      let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

      Self {
          same_context,
          shr_words,
      }
  }

  fn assign_exec_step(
      &self,
      region: &mut CachedRegion<'_, '_, F>,
      offset: usize,
      block: &Block<F>,
      _: &Transaction,
      _: &Call,
      step: &ExecStep,
  ) -> Result<(), Error> {
      self.same_context.assign_exec_step(region, offset, step)?;
      let indices = [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
      let [shift, a, b] = indices.map(|idx| block.rws[idx].stack_value());
      self.shr_words.assign(region, offset, a, shift, b)
  }
}

// ! 看起来主要是三部分的测试
#[cfg(test)]
mod test {
    // * 导入的库
    use crate::evm_circuit::test::rand_word;
    use crate::test_util::run_test_circuits;
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};
    use mock::TestContext;
    use rand::Rng;

    // * 主要的测试函数 -> 所有opcode都有一个test_ok
    // * 模拟在真实EVM执行环境下的opcode操作
    fn test_ok(opcode: OpcodeId, a: Word, shift: Word) {
        let bytecode = bytecode! {
            // * a和shift的类型都是EVM Word
            // * 分别PUSH进去`a`和`shift`
            PUSH32(a)
            PUSH32(shift)
            // * 准备执行
            #[start]
            // * 执行某一个Opcode -> 在这里是SHR或者SAR
            .write_op(opcode)
            // * 停止执行
            STOP
        };
        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn shr_gadget_simple() {
        // * 一共只需要传入三个参数 -> opcodeID, a, shift
        // * 这里所有的0x前缀，都是hex数据
        // * into()函数应该是把所有i32格式的数据，转换成U256 -> 因为EVM word就是u256
        test_ok(OpcodeId::SHR, 0xABCD.into(), 8.into());
        test_ok(OpcodeId::SHR, 0x1234.into(), 7.into());
        test_ok(OpcodeId::SHR, 0x8765.into(), 17.into());
        test_ok(OpcodeId::SHR, 0x4321.into(), 0.into());
        // * 这里是拿到一个EVM word（U256类型，目测是一个256-bit数据）
        // * rand_word()函数会用到`Rng`，所以需要一开始就导入scope内
        test_ok(OpcodeId::SHR, rand_word(), 127.into());
        test_ok(OpcodeId::SHR, rand_word(), 129.into());
        // * 给我的感觉，这里给了一个range范围，然后把所有值都用来shift算一遍 -> 直接给了一个最大的有效范围，从0到255
        // * 把一个EVM word从0到255，都shift一遍
        let rand_shift = rand::thread_rng().gen_range(0..=255);
        test_ok(OpcodeId::SHR, rand_word(), rand_shift.into());
    }

    #[test]
    // * 测试能否检测出overflow，lisp的comment也提到了这一点
    fn shr_gadget_rand_overflow_shift() {
        // * 256已经overflow
        // * 0x1234如果变成decimal是一个非常大的数（大概4660）
        test_ok(OpcodeId::SHR, rand_word(), 256.into());
        test_ok(OpcodeId::SHR, rand_word(), 0x1234.into());
        test_ok(
            OpcodeId::SHR,
            rand_word(),
            // * from_big_endian貌似是对256-bit对unsigned value的转换
            // * SAR中a和b是signed value，shift不是（只是移动的范围，不需要有符号）
            // * 这段我们直接照着写，应该就可以
            Word::from_big_endian(&[255_u8; 32]),
        );
    }

    // * 检测U256的shift？
    // This case validates if the split is correct.
    // * 用于验证split是否正确（how?）
    #[test]
    fn shr_gadget_constant_shift() {
        let a = rand_word();
        test_ok(OpcodeId::SHR, a, 8.into());
        test_ok(OpcodeId::SHR, a, 64.into());
    }
}