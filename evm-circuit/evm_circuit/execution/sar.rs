// ! 这是最古早版本的SAR opcode（2022年1月）
// * 我们需要对其做一些必要的修改，以让它成为最新版本

use crate::{
    // ! 导入的内容跟Shl_Shr几乎完全一样
    // * 除了一些shr使用到的lookup table和计算时用到的gadget（IsZeroGadget, MulAddWordsGadget）
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
            math_gadget::SarWordsGadget,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
// * 与SHL相比，多了`arithmetic::FieldExt`和`circuit::Region`
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct SarGadget<F> {
    same_context: SameContextGadget<F>,
    // * 正常来说，这里应该填一堆中间数据
    // * 不过可能是为了尽可能的降低代码复杂度，这里的中间数据被交给了math gadget的`SarWordsGadget`完成
    // * 最后再传给sar_words即可
    sar_words: SarWordsGadget<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for SarGadget<F> {
    const NAME: &'static str = "SAR";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SAR;

    // ! 设计目标：约束输入的a和shift，以及bitwise shift计算过程中的中间数据（保证计算结果正确）
    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        // * 两个input，作为EVM word，要有一些约束
        let a = cb.query_word();
        let shift = cb.query_word();

        // * POP出shift和a -> 然后计算，并且PUSH计算结果b
        cb.stack_pop(shift.expr());
        cb.stack_pop(a.expr());
        // ! SarWordsGadget进行具体的中间计算 -> 以及构建各种约束
        let sar_words = SarWordsGadget::construct(cb, a, shift);
        cb.stack_push(sar_words.b().expr());

        let step_state_transition = StepStateTransition {
            // * gc + 3 -> 2 stack read, 1 stack write
            rw_counter: Delta(3.expr()),
            // * pc + 1
            program_counter: Delta(1.expr()),
            // * stack_pointer + 1
            stack_pointer: Delta(1.expr()),
            // * 还有一个`gas + 3`，不知道这里为什么没有
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            // ! 这里为什么这么写？不消耗gas吗？
            None,
        );

        Self {
            same_context,
            sar_words,
        }
    }

    fn assign_exec_step(
        // * 一样，继承自trait，固定的参数
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction<F>,
        _: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        // ! 貌似是固定的步骤（same_context和indices）
        // * 之后研究一下到底什么作用
        self.same_context.assign_exec_step(region, offset, step)?;
        let indices =
            [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        // ! 这部分就是SAR独有的内容 -> shift和a作为input，b作为output
        // * 不知道是不是为了初始化indices，从而才能在stack中拿到数据，因为这里和SHL是一样的步骤
        let [shift, a, b] = indices.map(|idx| block.rws[idx].stack_value());
        // * 最后再把执行结果的数据assign
        // * 总的来看，这个opcode在这里比较简单，所以我估计复杂的逻辑都在math gadget里
        self.sar_words.assign(region, offset, a, shift, b)
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::{rand_word, run_test_circuit_incomplete_fixed_table},
        witness,
    };
    use bus_mapping::{bytecode, eth_types::Word, evm::OpcodeId};
    use rand::Rng;

    fn test_ok(opcode: OpcodeId, a: Word, shift: Word) {
        let bytecode = bytecode! {
            PUSH32(a)
            PUSH32(shift)
            #[start]
            .write_op(opcode)
            STOP
        };
        let block = witness::build_block_from_trace_code_at_start(&bytecode);
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn sar_gadget_simple() {
        test_ok(OpcodeId::SAR, 0x02FF.into(), 0x1.into());
        test_ok(
            OpcodeId::SAR,
            Word::from_big_endian(&[255u8; 32]),
            0x73.into(),
        );
    }

    #[test]
    fn sar_gadget_rand() {
        let a = rand_word();
        let mut rng = rand::thread_rng();
        let shift = rng.gen_range(0..=255);
        test_ok(OpcodeId::SAR, a, shift.into());
    }

    //this testcase manage to check the split is correct.
    #[test]
    fn sar_gadget_constant_shift() {
        let a = rand_word();
        test_ok(OpcodeId::SAR, a, 8.into());
        test_ok(OpcodeId::SAR, a, 64.into());
    }
}
