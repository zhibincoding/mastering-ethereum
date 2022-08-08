from __future__ import annotations
from typing import Sequence, Protocol, Type, TypeVar, Union
from py_ecc import bn128
from py_ecc.utils import prime_field_inv


def linear_combine(seq: Sequence[Union[int, FQ]], base: FQ, range_check: bool = True) -> FQ:
    """
    Aggregate a sequence of data into a single field element.
    To use it as a commitment, the base must be a secured random number.
    If the input represents a sequence of data, apply the function directly.
    If the input represents a number, it must be in little-endian order.
    >>> r = 10
    >>> assert linear_combine([1, 2, 3], r) == 1 + 2 * r + 3 * r**2
    """
    result = FQ.zero()
    for limb in reversed(seq):
        if range_check:
            limb_int = limb.n if isinstance(limb, FQ) else limb
            assert 0 <= limb_int < 256, "Each byte should fit in 8-bit"
        result = result * base + limb
    return result

# * 我们的FQ是bn128（椭圆曲线中的一种，BN curve）
class FQ(bn128.FQ):
    def __init__(self, value: IntOrFQ) -> None:
        # * 实例
        if isinstance(value, FQ):
            self.n = value.n
        else:
            super().__init__(value)

    def __hash__(self) -> int:
        # * 这个函数应该是计算hash
        return hash(self.n)

    def expr(self) -> FQ:
        return FQ(self)

    def inv(self) -> FQ:
        return FQ(prime_field_inv(self.n, self.field_modulus))


IntOrFQ = Union[int, FQ]

# * 参考这篇：https://learnblockchain.cn/books/geth/part3/rlp.html
# * 输入是bytes（array）或者其余值的序列（树状结构的集合）
class RLC:
    # value in int
    int_value: int
    # encoded value using `random linear combination`（随机线性组合）
    # * 解码数据
    rlc_value: FQ
    # bytes in `little-endian order`
    # * 有点像数据长度的东西
    le_bytes: bytes

    def __init__(self, value: Union[int, bytes], randomness: FQ = FQ(0), n_bytes: int = 32) -> None:
        # * 实例化一个value？
        if isinstance(value, int):
            value = value.to_bytes(n_bytes, "little")

        # * value超过了int=32的长度
        if len(value) > n_bytes:
            # * 弹出错误，看样子需要解析32长度的bytes
            raise ValueError(f"RLC expects to have {n_bytes} bytes, but got {len(value)} bytes")
        value = value.ljust(n_bytes, b"\x00")

        self.int_value = int.from_bytes(value, "little")
        self.rlc_value = linear_combine(value, randomness)
        self.le_bytes = value

    # * RLC主要就是一种数据压缩 + 数据存储方法
    def expr(self) -> FQ:
        return FQ(self.rlc_value)

    def __hash__(self) -> int:
        return hash(self.rlc_value)

    def __repr__(self) -> str:
        return "RLC(%s)" % int.from_bytes(self.le_bytes, "little")


class Expression(Protocol):
    def expr(self) -> FQ:
        ...


ExpressionImpl = TypeVar("ExpressionImpl", bound=Expression)


def cast_expr(expression: Expression, ty: Type[ExpressionImpl]) -> ExpressionImpl:
    if not isinstance(expression, ty):
        raise TypeError(f"Casting Expression to {ty}, but got {type(expression)}")
    return expression
