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

// * 每个opcode都要这样实现一个自己OpGadget
// * 然后里面分别有configure和assign（用来写constraint）

// * 继承了（不知道能不能这样说）ExecutionGadget trait的impl
// * 可以共享这个trait内定义的所有behavior
// * 所有opcode的通用写法应该都是这样 -> 定义两个const、两个function
// * 接下来我们要把所有const和function的含义和作用给搞懂

impl<F: Field> ExecutionGadget<F> for ShlShrGadget<F> {
    // * gadget的名字？
    const NAME: &'static str = "SHL_SHR";

    // * execution state -> 从step.rs文件的ExecutionState enum中取出对应的op
    const EXECUTION_STATE: ExecutionState = ExecutionState::SHL_SHR;

    // * ConstraintBuilder顾名思义，用来构造约束
    // * 跟ConstraintSystem一样，封装了很多API，可以用它们构造不同的constraint
    // ! 这两个函数的参数都是固定的，在trait中已经定义好
    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // ! 感觉需要理解halo2里面cell这个概念 -> 再往上就要懂Plonkish的一系列东西
        // * 我感觉cell可能是halo2 table里面的一个元素，query cell就是把这个元素拿出来
        // * 不知道opcode cell在哪个column里（advice还是instance）
        let opcode = cb.query_cell();
        // * 确定是哪个opcode -> shl还是shr
        let is_shl = OpcodeId::SHR.expr() - opcode.expr();
        let is_shr = 1.expr() - is_shl.expr();

        // * 不知道query word是什么，也是从table里面拿cell吗？
        // * 还是有一个专门存word的地方
        let quotient = cb.query_word();
        let divisor = cb.query_word();
        let remainder = cb.query_word();
        let dividend = cb.query_word();
        let shift = cb.query_word();
        // * 也从table里面拿出cell
        let shf0 = cb.query_cell();

        // * 有点像做初始化
        // * 1）比如这个就是`加法门`和`乘法门`的gadget
        // *    用来构建和约束 -> quotient * divisor + remainder = dividend
        let mul_add_words =
            // * 为什么传入这四个参数就足够了，不需要指定计算方式吗（+和*）？
            // * 因为我并没有在math gadget里面看到这个gadget的修改记录
            MulAddWordsGadget::construct(cb, [&quotient, &divisor, &remainder, &dividend]);
        // * 检查`divisor`是否为0
        let divisor_is_zero = IsZeroGadget::construct(cb, sum::expr(&divisor.cells));
        // * 检查`remainder`是否为0
        let remainder_is_zero = IsZeroGadget::construct(cb, sum::expr(&remainder.cells));
        // * 当divisor不为0的时候，检查remainder < divisor是否成立
        let remainder_lt_divisor = LtWordGadget::construct(cb, &remainder, &divisor);

        // Constrain stack pops and pushes as:
        // - for SHL, two pops are shift and quotient（商）, and push is dividend（除）.
        // - for SHR, two pops are shift and dividend（除）, and push is quotient（商）.
        // * 两个POP，一个PUSH
        cb.stack_pop(shift.expr());
        cb.stack_pop(is_shl.expr() * quotient.expr() + is_shr.expr() * dividend.expr());
        cb.stack_push(
            is_shl.expr() * dividend.expr()
                + is_shr.expr() * quotient.expr() * (1.expr() - divisor_is_zero.expr()),
        );

        // ! 这里具体构造的约束有一点看不懂，可能需要结合python spec代码
        // * require_zero貌似是一个构造constraint的API
        // * 构造的前提是，需要等式关系最终是0
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
        // * 类似于SAR的思路，把数据分成low和high
        // * 前16个数据是low，后16个数据是high
        let divisor_lo = from_bytes::expr(&divisor.cells[..16]);
        let divisor_hi = from_bytes::expr(&divisor.cells[16..]);
        cb.condition(1.expr() - divisor_is_zero.expr(), |cb| {
            // * 添加一个lookup table -> 暂不清楚具体作用
            // * Pow2是math gadget里面新增加的gadget
            cb.add_lookup(
                "Pow2 lookup of shf0, divisor_lo and divisor_hi",
                Lookup::Fixed {
                    tag: FixedTableTag::Pow2.expr(),
                    values: [shf0.expr(), divisor_lo.expr(), divisor_hi.expr()],
                },
            );
        });

        // * 约束每一步的state transition -> 有一些固定的参数
        // * 主要就是rw、pc、stack pointer、gas的数量要正确（在zkevm的spec里定义）
        // ! gc+3、stack_pointer+1、pc+1、gas+3
        let step_state_transition = StepStateTransition {
            // * gc+3 -> 这个应该是write什么的东西
            rw_counter: Delta(3.expr()),
            // * pc+1
            program_counter: Delta(1.expr()),
            // * stack_pointer+1
            stack_pointer: Delta(1.expr()),
            // * gas+3
            gas_left: Delta(-OpcodeId::SHL.constant_gas_cost().expr()),
            ..Default::default()
        };

        // * state_transition的生效依赖于same_context
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        // * 最后return的数据 -> 拿到所有configure出来的结果
        // * 在下一个函数中assign
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
        // * 这些都是trait中固定的参数
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        // * 全都是witness.rs中的数据类型
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        // * assign execution step
        self.same_context.assign_exec_step(region, offset, step)?;
        // * 貌似为了拿到对应的数据 -> indices、pop1 pop2 push、shf0
        let indices = [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        let [pop1, pop2, push] = indices.map(|idx| block.rws[idx].stack_value());
        let shf0 = pop1.to_le_bytes()[0];
        // * 这段数据之前使用过mul_add_gadget，可能就是为了让他们含有这个属性，在这里能够使用
        let (quotient, divisor, remainder, dividend) = match step.opcode.unwrap() {
            // * 应该分别是SHL和SHR的计算过程
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
                // ! SHR有这段约束关系
                (push, divisor, pop2 - push * divisor, pop2)
            }
            _ => unreachable!(),
        };
        // ! 各种约束，这部分没有完全理解
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
    // * 测试文件
    use crate::{evm_circuit::test::rand_word, test_util::run_test_circuits};
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};
    // * test的context，我看有chainID，还有geth_trace -> 进行测试应该主要就需要导入这些数据
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
