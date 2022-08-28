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
    fn test_ok(opcode: OpcodeId, a: Word, shift: Word) {
        let bytecode = bytecode! {
            PUSH32(a)
            PUSH32(shift)
            #[start]
            .write_op(opcode)
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

    // * 正常bitwise shift的计算
    #[test]
    fn shr_gadget_simple() {
        test_ok(OpcodeId::SHR, 0xABCD.into(), 8.into());
        test_ok(OpcodeId::SHR, 0x1234.into(), 7.into());
        test_ok(OpcodeId::SHR, 0x8765.into(), 17.into());
        test_ok(OpcodeId::SHR, 0x4321.into(), 0.into());
        test_ok(OpcodeId::SHR, rand_word(), 127.into());
        test_ok(OpcodeId::SHR, rand_word(), 129.into());
        let rand_shift = rand::thread_rng().gen_range(0..=255);
        test_ok(OpcodeId::SHR, rand_word(), rand_shift.into());
    }

    // * 检测overflow shift
    #[test]
    fn shr_gadget_rand_overflow_shift() {
        test_ok(OpcodeId::SHR, rand_word(), 256.into());
        test_ok(OpcodeId::SHR, rand_word(), 0x1234.into());
        test_ok(
            OpcodeId::SHR,
            rand_word(),
            Word::from_big_endian(&[255_u8; 32]),
        );
    }

    // * 检测U256的shift？
    // This case validates if the split is correct.
    #[test]
    fn shr_gadget_constant_shift() {
        let a = rand_word();
        test_ok(OpcodeId::SHR, a, 8.into());
        test_ok(OpcodeId::SHR, a, 64.into());
    }
}
