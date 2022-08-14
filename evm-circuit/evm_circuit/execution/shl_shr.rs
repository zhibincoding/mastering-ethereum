use crate::{
  // * 在zkevm-circuits/src/evm_circuit.rs文件下
  // * 可以理解这是一个evm circuit实现，包裹了所有evm circuit内部的组件
  // * 所以可以从这里面导入所有的context模块
  evm_circuit::{
  // ! 在这里导入的都是src/evm_circuit/之下的文件
      // * 注册所有opcode和error case的那个struct
      execution::ExecutionGadget,
      // * 也是所有opcode的enum
      step::ExecutionState,
      // * 会有7个tables：Fixed、Tx、RW、Bytecode、Block、Byte、CopyTable
      // * FixedTableTag貌似也是一个有用的工具，我们之前看到的PoW2也在里面，不过暂不清楚实际作用是什么
      table::{FixedTableTag, Lookup},
      util::{
          // * 1.分别导入util.rs这个文件
          // * 2.以及util/文件夹内的不同.rs模块 -> 都是一些gadget工具
          // *   比如`common gadget`, `constraint builder`, `math gadget`, `memory gadget`
          self,
          common_gadget::SameContextGadget,
          constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
          // * 这个是util.rs内的
          from_bytes,
          math_gadget::{IsZeroGadget, LtWordGadget, MulAddWordsGadget},
          // * 这个也是util.rs内的
          sum, CachedRegion, Cell,
      },
      // * witness.rs文件 -> 里面有各种bus-mapping转换的zkevm trace数据
      witness::{Block, Call, ExecStep, Transaction},
  },
  // ! 这个直接导入src/路径下的util，与evm_circuit/同一路径
  util::Expr,
};
// * 用来mapping不同的opcode -> 使用OpcodeId
use bus_mapping::evm::OpcodeId;
// * 这里应该是一些直接在EVM定义的数据类型
// * Ethereum and Evm types used to deserialize responses from web3 / geth
// * 👆对应注释说是用来`deserialize responses`
use eth_types::{Field, ToLittleEndian, U256};
// * 是一个enums
// * 应该是在使用halo2 api写电路过程中，可能会遇到的所有error case
use halo2_proofs::plonk::Error;

// ! 可以直接参考`ShrWordsGadget`: https://www.overleaf.com/project/62d1ba4a752d1fcbe66e9340
/// ShlShrGadget verifies opcode SHL and SHR.
/// For SHL, verify pop1 * (2^pop2) == push;
/// For SHR, verify pop1 / (2^pop2) = push;
/// when pop1, pop2, push are 256-bit words.
#[derive(Clone, Debug)]
pub(crate) struct ShlShrGadget<F> {
  // * 貌似可以直接参考: https://www.overleaf.com/project/62d1ba4a752d1fcbe66e9340
  // * 在同一个call context里面，约束state transition
  same_context: SameContextGadget<F>,
  // ! 这些都是word
  // * 也就意味着256-bit
  // ! 不太清楚这里为什么有一堆除法运算的数据，后面可以看看怎么用的
  // ! 我估计是在bitwise shift中间操作的时候，进行的一堆中间计算过程
  // ! 这些是SHL_SHR的中间计算过程 -> quotient * divisor + remainder = dividend (% 2^256)
  // * 商
  quotient: util::Word<F>,
  // * 除数
  divisor: util::Word<F>,
  // * 余数
  remainder: util::Word<F>,
  // * 股息
  dividend: util::Word<F>,
  /// Shift word
  // * shift和shf0都在spec里有定义
  shift: util::Word<F>,
  /// First byte of shift word
  shf0: Cell<F>,
  // * 👆上面的都是spec里面，用来输入gen_witness函数，生成witness的参数
  // * 👇下面的都是一些证明时需要用到的gadget
  /// Gadget that verifies quotient * divisor + remainder = dividend
  mul_add_words: MulAddWordsGadget<F>,
  /// Check if divisor is zero
  divisor_is_zero: IsZeroGadget<F>,
  /// Check if remainder is zero
  remainder_is_zero: IsZeroGadget<F>,
  /// Check if remainder < divisor when divisor != 0
  remainder_lt_divisor: LtWordGadget<F>,
}

// * 貌似每个opcode都要这样实现一个自己OpcodeGadget
// * 然后里面分别有configure和assign（用来写constraint）
impl<F: Field> ExecutionGadget<F> for ShlShrGadget<F> {
  const NAME: &'static str = "SHL_SHR";

  const EXECUTION_STATE: ExecutionState = ExecutionState::SHL_SHR;

  fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
      let opcode = cb.query_cell();
      let is_shl = OpcodeId::SHR.expr() - opcode.expr();
      let is_shr = 1.expr() - is_shl.expr();

      let quotient = cb.query_word();
      let divisor = cb.query_word();
      let remainder = cb.query_word();
      let dividend = cb.query_word();
      let shift = cb.query_word();
      let shf0 = cb.query_cell();

      let mul_add_words =
          MulAddWordsGadget::construct(cb, [&quotient, &divisor, &remainder, &dividend]);
      let divisor_is_zero = IsZeroGadget::construct(cb, sum::expr(&divisor.cells));
      let remainder_is_zero = IsZeroGadget::construct(cb, sum::expr(&remainder.cells));
      let remainder_lt_divisor = LtWordGadget::construct(cb, &remainder, &divisor);

      // Constrain stack pops and pushes as:
      // - for SHL, two pops are shift and quotient, and push is dividend.
      // - for SHR, two pops are shift and dividend, and push is quotient.
      cb.stack_pop(shift.expr());
      cb.stack_pop(is_shl.expr() * quotient.expr() + is_shr.expr() * dividend.expr());
      cb.stack_push(
          is_shl.expr() * dividend.expr()
              + is_shr.expr() * quotient.expr() * (1.expr() - divisor_is_zero.expr()),
      );

      cb.require_zero(
          "shift == shift.cells[0] when divisor != 0",
          (1.expr() - divisor_is_zero.expr()) * (shift.expr() - shift.cells[0].expr()),
      );

      cb.require_zero(
          "remainder < divisor when divisor != 0",
          (1.expr() - divisor_is_zero.expr()) * (1.expr() - remainder_lt_divisor.expr()),
      );

      cb.require_zero(
          "remainder == 0 for opcode SHL",
          is_shl * (1.expr() - remainder_is_zero.expr()),
      );

      cb.require_zero(
          "overflow == 0 for opcode SHR",
          is_shr * mul_add_words.overflow(),
      );

      // Constrain divisor_lo == 2^shf0 when shf0 < 128, and
      // divisor_hi == 2^(128 - shf0) otherwise.
      let divisor_lo = from_bytes::expr(&divisor.cells[..16]);
      let divisor_hi = from_bytes::expr(&divisor.cells[16..]);
      cb.condition(1.expr() - divisor_is_zero.expr(), |cb| {
          cb.add_lookup(
              "Pow2 lookup of shf0, divisor_lo and divisor_hi",
              Lookup::Fixed {
                  tag: FixedTableTag::Pow2.expr(),
                  values: [shf0.expr(), divisor_lo.expr(), divisor_hi.expr()],
              },
          );
      });

      let step_state_transition = StepStateTransition {
          rw_counter: Delta(3.expr()),
          program_counter: Delta(1.expr()),
          stack_pointer: Delta(1.expr()),
          gas_left: Delta(-OpcodeId::SHL.constant_gas_cost().expr()),
          ..Default::default()
      };

      let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

      Self {
          same_context,
          quotient,
          divisor,
          remainder,
          dividend,
          shift,
          shf0,
          mul_add_words,
          divisor_is_zero,
          remainder_is_zero,
          remainder_lt_divisor,
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
      let [pop1, pop2, push] = indices.map(|idx| block.rws[idx].stack_value());
      let shf0 = pop1.to_le_bytes()[0];
      let (quotient, divisor, remainder, dividend) = match step.opcode.unwrap() {
          OpcodeId::SHL => (
              pop2,
              if U256::from(shf0) == pop1 {
                  U256::from(1) << shf0
              } else {
                  U256::from(0)
              },
              U256::from(0),
              push,
          ),
          OpcodeId::SHR => {
              let divisor = if U256::from(shf0) == pop1 {
                  U256::from(1) << shf0
              } else {
                  U256::from(0)
              };
              (push, divisor, pop2 - push * divisor, pop2)
          }
          _ => unreachable!(),
      };
      self.quotient
          .assign(region, offset, Some(quotient.to_le_bytes()))?;
      self.divisor
          .assign(region, offset, Some(divisor.to_le_bytes()))?;
      self.remainder
          .assign(region, offset, Some(remainder.to_le_bytes()))?;
      self.dividend
          .assign(region, offset, Some(dividend.to_le_bytes()))?;
      self.shift
          .assign(region, offset, Some(pop1.to_le_bytes()))?;
      self.shf0
          .assign(region, offset, Some(u64::from(shf0).into()))?;
      self.mul_add_words
          .assign(region, offset, [quotient, divisor, remainder, dividend])?;
      let divisor_sum = (0..32).fold(0, |acc, idx| acc + divisor.byte(idx) as u64);
      self.divisor_is_zero
          .assign(region, offset, F::from(divisor_sum))?;
      let remainder_sum = (0..32).fold(0, |acc, idx| acc + remainder.byte(idx) as u64);
      self.remainder_is_zero
          .assign(region, offset, F::from(remainder_sum))?;
      self.remainder_lt_divisor
          .assign(region, offset, remainder, divisor)
  }
}

#[cfg(test)]
mod test {
  use crate::{evm_circuit::test::rand_word, test_util::run_test_circuits};
  use eth_types::evm_types::OpcodeId;
  use eth_types::{bytecode, Word};
  use mock::TestContext;

  fn test_ok(opcode: OpcodeId, pop1: Word, pop2: Word) {
      let bytecode = bytecode! {
          PUSH32(pop1)
          PUSH32(pop2)
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

  #[test]
  fn shl_gadget_tests() {
      test_ok(OpcodeId::SHL, Word::from(0xABCD) << 240, Word::from(8));
      test_ok(OpcodeId::SHL, Word::from(0x1234) << 240, Word::from(7));
      test_ok(OpcodeId::SHL, Word::from(0x8765) << 240, Word::from(17));
      test_ok(OpcodeId::SHL, Word::from(0x4321) << 240, Word::from(0));
      test_ok(OpcodeId::SHL, Word::from(0xFFFF), Word::from(256));
      test_ok(OpcodeId::SHL, Word::from(0x12345), Word::from(256 + 8 + 1));
      let max_word = Word::from_big_endian(&[255_u8; 32]);
      test_ok(OpcodeId::SHL, max_word, Word::from(63));
      test_ok(OpcodeId::SHL, max_word, Word::from(128));
      test_ok(OpcodeId::SHL, max_word, Word::from(129));
      test_ok(OpcodeId::SHL, rand_word(), rand_word());
  }

  #[test]
  fn shr_gadget_tests() {
      test_ok(OpcodeId::SHR, Word::from(0xABCD), Word::from(8));
      test_ok(OpcodeId::SHR, Word::from(0x1234), Word::from(7));
      test_ok(OpcodeId::SHR, Word::from(0x8765), Word::from(17));
      test_ok(OpcodeId::SHR, Word::from(0x4321), Word::from(0));
      test_ok(OpcodeId::SHR, Word::from(0xFFFF), Word::from(256));
      test_ok(OpcodeId::SHR, Word::from(0x12345), Word::from(256 + 8 + 1));
      let max_word = Word::from_big_endian(&[255_u8; 32]);
      test_ok(OpcodeId::SHR, max_word, Word::from(63));
      test_ok(OpcodeId::SHR, max_word, Word::from(128));
      test_ok(OpcodeId::SHR, max_word, Word::from(129));
      test_ok(OpcodeId::SHR, rand_word(), rand_word());
  }
}
