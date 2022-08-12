# 这里导入了三个util
# * 1）FQ -> 在arithmetic.py里
# * 2）N_BYTES_U64 -> 在param.py里
# * 3）RLC -> 在arithmetic.py里2
from ...util import FQ, N_BYTES_U64, RLC
from ..instruction import Instruction, Transition
from ..opcode import Opcode
from ..typing import Sequence

# 18446744073709551615
MAX_U64 = 0xFFFFFFFFFFFFFFFF

# * 状态的转变
def sar(instruction: Instruction):
    opcode = instruction.opcode_lookup(True)

    a = instruction.stack_pop()
    shift = instruction.stack_pop()
    b = instruction.stack_push()

    (
        a64s,
        b64s,
        a64s_lo,
        a64s_hi,
        shf_div64,
        shf_mod64,
        p_lo,
        p_hi,
        p_top,
        is_neg,
    ) = __gen_witness(instruction, opcode, a, shift)
    __check_witness(
        instruction,
        a,
        shift,
        b,
        a64s,
        b64s,
        a64s_lo,
        a64s_hi,
        shf_div64,
        shf_mod64,
        p_lo,
        p_hi,
        p_top,
        is_neg,
    )

    # gc + 3 (2 stack reads + 1 stack write)
    # gas + 3
    instruction.step_state_transition_in_same_context(
        opcode,
        rw_counter=Transition.delta(2),
        # pc + 1
        program_counter=Transition.delta(1),
        # stack_pointer + 1
        stack_pointer=Transition.delta(1),
    )

# * 检查witness，写一些gadgets做检查
def __check_witness(
    # * 传入各种witness数据，并且定义数据类型
    # * 剩下的就是做各种constraint
    instruction: Instruction,
    a: RLC,
    shift: RLC,
    b: RLC,
    a64s: Sequence[FQ],
    b64s: Sequence[FQ],
    a64s_lo: Sequence[FQ],
    a64s_hi: Sequence[FQ],
    shf_div64,
    shf_mod64,
    p_lo,
    p_hi,
    p_top,
    is_neg,
):
    shf_lt256 = instruction.is_zero(instruction.sum(shift.le_bytes[1:]))
    for idx in range(4):
        offset = idx * N_BYTES_U64

        # a64s constraint
        instruction.constrain_equal(
            a64s[idx],
            instruction.bytes_to_fq(a.le_bytes[offset : offset + N_BYTES_U64]),
        )

        # b64s constraint
        instruction.constrain_equal(
            b64s[idx] * shf_lt256 + is_neg * (1 - shf_lt256) * MAX_U64,
            instruction.bytes_to_fq(b.le_bytes[offset : offset + N_BYTES_U64]),
        )

        # `a64s[idx] == a64s_lo[idx] + a64s_hi[idx] * p_lo`
        instruction.constrain_equal(a64s[idx], a64s_lo[idx] + a64s_hi[idx] * p_lo)

        # `a64s_lo[idx] < p_lo`
        a64s_lo_lt_p_lo, _ = instruction.compare(a64s_lo[idx], p_lo, N_BYTES_U64)
        instruction.constrain_equal(a64s_lo_lt_p_lo, FQ(1))

    # merge contraints
    
    shf_div64_eq0 = instruction.is_zero(shf_div64)
    shf_div64_eq1 = instruction.is_zero(shf_div64 - 1)
    shf_div64_eq2 = instruction.is_zero(shf_div64 - 2)
    shf_div64_eq3 = instruction.is_zero(shf_div64 - 3)
    instruction.constrain_equal(
        b64s[0],
        (a64s_hi[0] + a64s_lo[1] * p_hi) * shf_div64_eq0
        + (a64s_hi[1] + a64s_lo[2] * p_hi) * shf_div64_eq1
        + (a64s_hi[2] + a64s_lo[3] * p_hi) * shf_div64_eq2
        + (a64s_hi[3] + p_top) * shf_div64_eq3
        + is_neg * MAX_U64 * (1 - shf_div64_eq0 - shf_div64_eq1 - shf_div64_eq2 - shf_div64_eq3),
    )
    instruction.constrain_equal(
        b64s[1],
        (a64s_hi[1] + a64s_lo[2] * p_hi) * shf_div64_eq0
        + (a64s_hi[2] + a64s_lo[3] * p_hi) * shf_div64_eq1
        + (a64s_hi[3] + p_top) * shf_div64_eq2
        + is_neg * MAX_U64 * (1 - shf_div64_eq0 - shf_div64_eq1 - shf_div64_eq2),
    )
    instruction.constrain_equal(
        b64s[2],
        (a64s_hi[2] + a64s_lo[3] * p_hi) * shf_div64_eq0
        + (a64s_hi[3] + p_top) * shf_div64_eq1
        + is_neg * MAX_U64 * (1 - shf_div64_eq0 - shf_div64_eq1),
    )
    instruction.constrain_equal(
        b64s[3],
        (a64s_hi[3] + p_top) * shf_div64_eq0 + is_neg * MAX_U64 * (1 - shf_div64_eq0),
    )

    # shift constraint
    instruction.constrain_equal(
        instruction.bytes_to_fq(shift.le_bytes[:1]),
        shf_mod64 + shf_div64 * 64,
    )

    # `p_lo == pow(2, shf_mod64)` and `p_hi == pow(2, 64 - shf_mod64)`.
    instruction.pow2_lookup(shf_mod64, p_lo)
    instruction.pow2_lookup(64 - shf_mod64, p_hi)

# * 生成witness数据 -> 这些数据是什么样的形式？
# * 貌似全都是EVM word拆分以后/并且shift以后的a64s等
# ! 1.传入a和shift，都是RLC编码格式
def __gen_witness(instruction: Instruction, opcode: FQ, a: RLC, shift: RLC):
    # Opcode of SHR and SAR are 0x1C and 0x1D. Result is 1 for SAR and 0 for SHR.
    # * 检查是哪个opcode，是SHR还是SAR
    is_sar = opcode - Opcode.SHR  # 0x1C

    # * 判断是否是负数
    is_neg = is_sar * instruction.word_is_neg(a)
    # * bytes_to_fq函数传入`value: bytes`，返回FQ
    # * 在这里是否可以简单理解把shift的数据类型做了一个转换？
    # * 1）一方面是一个数据转换，bytes转换成FQ上的数据
    # * 2）另一方面 `[:1]` 貌似是为了限制 bytes < 256
    # ! 这里的[:1]什么意思，跟我理解的一样吗
    shf0 = instruction.bytes_to_fq(shift.le_bytes[:1])
    # * 如果 256 // 64 = 4
    # * 如果 255 // 64 = 3.984375
    # ! 这里的n是什么东西？取长度吗？
    # * 这里应该是粉分成几个不同的limbs，每个64-bit
    shf_div64 = FQ(shf0.n // 64)
    # * 如果 255 % 64 = 63（只能整除掉3个64）
    shf_mod64 = FQ(shf0.n % 64)
    # * 这个类似做shift操作，然后取出高位和低位的数据
    # * 比如11110000，shift以后就取出高位数字`1111`
    p_lo = FQ(1 << shf_mod64.n)
    p_hi = FQ(1 << (64 - shf_mod64.n))
    # The new bits are set to 1 if negative.
    # * 如果是负数，is_neg是 1
    # * MAX_U64是FFFFFFFFFFFFFFFF，一共8byte，64-bit -> 就是一个limb里面可以填的最大数据
    # ! 没看懂这里的计算过程 -> 不过如果是SAR，就把top new bits设置为1
    p_top = FQ(is_neg * (MAX_U64 - p_hi + 1))

    # * 这里貌似会做一个操作，把word分成四段limbs
    a64s = instruction.word_to_64s(a)
    # Each of the four `a64s` limbs is split into two parts (`a64s_lo` and `a64s_hi`)
    # at position `shf_mod64`. `a64s_lo` is the lower `shf_mod64` bits.
    # * 1.在shf_mod64会把一个limb拆成high和low
    # *   也就是 `a64s_lo` 和 `a64s_hi`
    a64s_lo = [FQ(0)] * 4
    a64s_hi = [FQ(0)] * 4
    for idx in range(4):
        # * 2.四个limbs都进行分拆
        a64s_lo[idx] = FQ(a64s[idx].n % p_lo.n)
        a64s_hi[idx] = FQ(a64s[idx].n // p_lo.n)

    # * b64s是shift之后的字段
    b64s = [instruction.select(is_neg, FQ(MAX_U64), FQ(0))] * 4
    # ! 这部分没有看太明白
    # * 这里其实是给b64s做初始化
    b64s[3 - shf_div64.n] = a64s_hi[3] + p_top
    for k in range(3 - shf_div64.n):
        b64s[k] = a64s_hi[k + shf_div64.n] + a64s_lo[k + shf_div64.n + 1] * p_hi

    # * 计算一遍，生成所有的witness
    # * 虽然有一些binary的中间计算过程我没看懂，不过不造成太大的影响
    return (
        # shift之前的字段
        a64s,
        # shift之后的字段
        b64s,
        # a64s分拆的low和high
        a64s_lo,
        a64s_hi,
        # ! 一个不确定的中间过程，貌似是用来分拆limbs
        shf_div64,
        shf_mod64,
        # * 貌似是shf_mod64最终的产出
        p_lo,
        p_hi,
        # 判断是否negative + 以及如果为负 p_top设置为1
        p_top,
        is_neg,
    )

# * python写完 -> 写circuit做验证（这里可能是sar_test）-> 再写markdown