// ! SAR版本的math gadget（2022年1月的版本）
// * 旧版本的代码结构其实也不简单，最新版本大概1500 row，旧版本有1200 row

use crate::{
  evm_circuit::{
      param::MAX_BYTES_FIELD,
      table::{FixedTableTag, Lookup},
      util::{
          self, constraint_builder::ConstraintBuilder, from_bytes,
          pow_of_two, pow_of_two_expr, select, split_u256, sum, Cell,
      },
  },
  util::Expr,
};
use bus_mapping::eth_types::{ToLittleEndian, Word};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
  inverse: Cell<F>,
  is_zero: Expression<F>,
}

impl<F: FieldExt> IsZeroGadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      value: Expression<F>,
  ) -> Self {
      let inverse = cb.query_cell();

      let is_zero = 1.expr() - (value.clone() * inverse.expr());
      // when `value != 0` check `inverse = a.invert()`: value * (1 - value *
      // inverse)
      cb.add_constraint(
          "value ⋅ (1 - value ⋅ value_inv)",
          value * is_zero.clone(),
      );
      // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value *
      // inverse)`
      cb.add_constraint(
          "value_inv ⋅ (1 - value ⋅ value_inv)",
          inverse.expr() * is_zero.clone(),
      );

      Self { inverse, is_zero }
  }

  pub(crate) fn expr(&self) -> Expression<F> {
      self.is_zero.clone()
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      value: F,
  ) -> Result<F, Error> {
      let inverse = value.invert().unwrap_or(F::zero());
      self.inverse.assign(region, offset, Some(inverse))?;
      Ok(if value.is_zero().into() {
          F::one()
      } else {
          F::zero()
      })
  }
}

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualGadget<F> {
  is_zero: IsZeroGadget<F>,
}

impl<F: FieldExt> IsEqualGadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      lhs: Expression<F>,
      rhs: Expression<F>,
  ) -> Self {
      let is_zero = IsZeroGadget::construct(cb, lhs - rhs);

      Self { is_zero }
  }

  pub(crate) fn expr(&self) -> Expression<F> {
      self.is_zero.expr()
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      lhs: F,
      rhs: F,
  ) -> Result<F, Error> {
      self.is_zero.assign(region, offset, lhs - rhs)
  }
}

/// Construction of 2 256-bit words addition and result, which is useful for
/// opcode ADD, SUB and balance operation
#[derive(Clone, Debug)]
pub(crate) struct AddWordsGadget<F, const N: usize> {
  addends: [util::Word<F>; N],
  sum: util::Word<F>,
  carry_lo: Cell<F>,
  carry_hi: Cell<F>,
}

impl<F: FieldExt, const N: usize> AddWordsGadget<F, N> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      addends: [util::Word<F>; N],
  ) -> Self {
      let sum = cb.query_word();
      let carry_lo = cb.query_cell();
      let carry_hi = cb.query_cell();

      let addends_lo = &addends
          .iter()
          .map(|addend| from_bytes::expr(&addend.cells[..16]))
          .collect::<Vec<_>>();
      let addends_hi = &addends
          .iter()
          .map(|addend| from_bytes::expr(&addend.cells[16..]))
          .collect::<Vec<_>>();
      let sum_lo = from_bytes::expr(&sum.cells[..16]);
      let sum_hi = from_bytes::expr(&sum.cells[16..]);

      cb.require_equal(
          "sum(addends_lo) == sum_lo + carry_lo ⋅ 2^128",
          sum::expr(addends_lo),
          sum_lo + carry_lo.expr() * pow_of_two_expr(128),
      );
      cb.require_equal(
          "sum(addends_hi) + carry_lo == sum_hi + carry_hi ⋅ 2^128",
          sum::expr(addends_hi) + carry_lo.expr(),
          sum_hi + carry_hi.expr() * pow_of_two_expr(128),
      );

      for carry in [&carry_lo, &carry_hi] {
          cb.require_in_set(
              "carry_lo in 0..N",
              carry.expr(),
              (0..N).map(|idx| idx.expr()).collect(),
          );
      }

      Self {
          addends,
          sum,
          carry_lo,
          carry_hi,
      }
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      addends: [Word; N],
      sum: Word,
  ) -> Result<(), Error> {
      for (word, value) in self.addends.iter().zip(addends.iter()) {
          word.assign(region, offset, Some(value.to_le_bytes()))?;
      }
      self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;

      let (addends_lo, addends_hi): (Vec<_>, Vec<_>) =
          addends.iter().map(split_u256).unzip();
      let (sum_lo, sum_hi) = split_u256(&sum);

      let sum_of_addends_lo = addends_lo
          .into_iter()
          .fold(Word::zero(), |acc, addend_lo| acc + addend_lo);
      let sum_of_addends_hi = addends_hi
          .into_iter()
          .fold(Word::zero(), |acc, addend_hi| acc + addend_hi);

      let carry_lo = (sum_of_addends_lo - sum_lo) >> 128;
      let carry_hi = (sum_of_addends_hi + carry_lo - sum_hi) >> 128;
      self.carry_lo.assign(
          region,
          offset,
          Some(F::from(carry_lo.low_u64())),
      )?;
      self.carry_hi.assign(
          region,
          offset,
          Some(F::from(carry_hi.low_u64())),
      )?;

      Ok(())
  }

  pub(crate) fn sum(&self) -> &util::Word<F> {
      &self.sum
  }

  pub(crate) fn carry(&self) -> &util::Cell<F> {
      &self.carry_hi
  }
}

/// Construction of 2 256-bit words mutiplication and result (modulo 2**256),
/// which is useful for opcode MUL, DIV, SDIV and xxxMOD
#[derive(Clone, Debug)]
pub(crate) struct MulWordsGadget<F> {
  a: util::Word<F>,
  b: util::Word<F>,
  product: util::Word<F>,
  //here we execute a multi-limbs multiplication, see spec or
  //https://hackmd.io/HL0QhGUeQoSgIBt2el6fHA
  // a, b and product is divided into 4 64-bit digits, call them a0 ~ a3, b0
  // ~ b3 ... a * b = a0 * b0 + a1 * b0 ..., and let
  // t0 = a0 * b0, contribute to 0 ~ 128 bit
  // t1 = a0 * b1 + a1 * b0, contribute to 64 ~ 193 bit (include the carry)
  // t2 = a0 * b2 + a2 * b0 + a1 * b1, contribute to above 128 bit
  // t3 =  a0 * b3 + a3 * b0 + a2 * b1 + a1 * b2, contribute to above 192 bit
  //
  // so t0 ~ t1 include all contributions to the low 256bit of product,
  // with a maxium 68bit radix (the part higher than 256bit) v1
  // it is similar that we have v0 as the radix of contributions
  // to the low 128bit of the product
  // we can slightly relax the constraint of v0/v1 to 72bit so just
  // use 9 bytes for them
  v0: [Cell<F>; 9],
  v1: [Cell<F>; 9],
  /* finally we just prove:
   *  t0 + t1 = <low 128 bit of product> + <radix v0>
   *  t2 + t3 + <radix v0> = <high 128 bit of product> + <radix v1> */
}

impl<F: FieldExt> MulWordsGadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      a: util::Word<F>,
      b: util::Word<F>,
  ) -> Self {
      let product = cb.query_word();
      let v0 = array_init::array_init(|_| cb.query_byte());
      let v1 = array_init::array_init(|_| cb.query_byte());

      let mut a_limbs = vec![];
      let mut b_limbs = vec![];
      let mut c_limbs = vec![];
      for virtual_idx in 0..4 {
          let now_idx = (virtual_idx * 8) as usize;
          a_limbs.push(from_bytes::expr(&a.cells[now_idx..now_idx + 8]));
          b_limbs.push(from_bytes::expr(&b.cells[now_idx..now_idx + 8]));
          c_limbs
              .push(from_bytes::expr(&product.cells[now_idx..now_idx + 8]));
      }

      let t0 = a_limbs[0].clone() * b_limbs[0].clone();
      let t1 = a_limbs[0].clone() * b_limbs[1].clone()
          + a_limbs[1].clone() * b_limbs[0].clone();
      let t2 = a_limbs[0].clone() * b_limbs[2].clone()
          + a_limbs[1].clone() * b_limbs[1].clone()
          + a_limbs[2].clone() * b_limbs[0].clone();
      let t3 = a_limbs[0].clone() * b_limbs[3].clone()
          + a_limbs[1].clone() * b_limbs[2].clone()
          + a_limbs[2].clone() * b_limbs[1].clone()
          + a_limbs[3].clone() * b_limbs[0].clone();

      let cur_v0 = from_bytes::expr(&v0[..]);
      let cur_v1 = from_bytes::expr(&v1[..]);

      //radix_constant_64 == 2^64
      //radix_constant_128 == 2^128
      let radix_constant_64 = pow_of_two_expr(64);
      let radix_constant_128 = pow_of_two_expr(128);
      cb.require_equal(
          "mul(multipliers_lo) == product_lo + radix_lo ⋅ 2^128",
          cur_v0.clone() * radix_constant_128.clone(),
          t0.expr() + t1.expr() * radix_constant_64.clone()
              - (c_limbs[0].clone()
                  + c_limbs[1].clone() * radix_constant_64.clone()),
      );
      cb.require_equal(
          "mul(multipliers_high) == product_high + radix_high ⋅ 2^128",
          cur_v1 * radix_constant_128,
          cur_v0 + t2.expr() + t3.expr() * radix_constant_64.clone()
              - (c_limbs[2].clone() + c_limbs[3].clone() * radix_constant_64),
      );

      Self {
          a,
          b,
          product,
          v0,
          v1,
      }
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      a: Word,
      b: Word,
      product: Word,
  ) -> Result<(), Error> {
      self.assign_witness(region, offset, &a, &b, &product)?;
      self.a.assign(region, offset, Some(a.to_le_bytes()))?;
      self.b.assign(region, offset, Some(b.to_le_bytes()))?;
      self.product
          .assign(region, offset, Some(product.to_le_bytes()))?;
      Ok(())
  }

  pub(crate) fn product(&self) -> &util::Word<F> {
      &self.product
  }

  //assign t0 ~ t3 and v0, v1
  fn assign_witness(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      wa: &Word,
      wb: &Word,
      wc: &Word,
  ) -> Result<(), Error> {
      use num::BigUint;

      let a = BigUint::from_bytes_le(&wa.to_le_bytes());
      let b = BigUint::from_bytes_le(&wb.to_le_bytes());
      let c = BigUint::from_bytes_le(&wc.to_le_bytes());
      let constant_64 = BigUint::from(1u128 << 64);
      let constant_128 = constant_64.clone() * constant_64.clone();
      let a_limbs = a.to_u64_digits();
      let b_limbs = b.to_u64_digits();
      let c_limbs = c.to_u64_digits();
      let mut t_digits = vec![];
      for total_idx in 0..4 {
          let mut rhs_sum = BigUint::from(0u128);
          for a_id in 0..=total_idx {
              let (a_idx, b_idx) =
                  (a_id as usize, (total_idx - a_id) as usize);
              let tmp_a = if a_limbs.len() > a_idx {
                  BigUint::from(a_limbs[a_idx])
              } else {
                  BigUint::from(0u128)
              };
              let tmp_b = if b_limbs.len() > b_idx {
                  BigUint::from(b_limbs[b_idx])
              } else {
                  BigUint::from(0u128)
              };
              rhs_sum = rhs_sum.clone() + tmp_a * tmp_b;
          }
          t_digits.push(rhs_sum);
      }

      let mut c_now = vec![];
      for idx in 0..4 {
          c_now.push(if c_limbs.len() > idx {
              BigUint::from(c_limbs[idx])
          } else {
              BigUint::from(0u128)
          })
      }
      let v0 = (constant_64.clone() * &t_digits[1] + &t_digits[0]
          - &c_now[0]
          - constant_64.clone() * &c_now[1])
          / &constant_128;
      let v1 = (constant_64.clone() * &t_digits[3] + &v0 + &t_digits[2]
          - &c_now[2]
          - constant_64 * &c_now[3])
          / &constant_128;

      v0.to_bytes_le()
          .into_iter()
          .zip(self.v0.iter())
          .try_for_each(|(bt, assignee)| -> Result<(), Error> {
              assignee.assign(region, offset, Some(F::from(bt as u64)))?;
              Ok(())
          })?;

      v1.to_bytes_le()
          .into_iter()
          .zip(self.v1.iter())
          .try_for_each(|(bt, assignee)| -> Result<(), Error> {
              assignee.assign(region, offset, Some(F::from(bt as u64)))?;
              Ok(())
          })?;

      Ok(())
  }
}

/// Construction of 256-bit product by 256-bit multiplicand * 64-bit multiplier.
#[derive(Clone, Debug)]
pub(crate) struct MulWordByU64Gadget<F> {
  multiplicand: util::Word<F>,
  multiplier: util::Cell<F>,
  product: util::Word<F>,
  carry_lo: [util::Cell<F>; 8],
  carry_hi: [util::Cell<F>; 8],
}

impl<F: FieldExt> MulWordByU64Gadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      multiplicand: util::Word<F>,
      multiplier: util::Cell<F>,
      check_overflow: bool,
  ) -> Self {
      let gadget = Self {
          multiplicand,
          multiplier,
          product: cb.query_word(),
          carry_lo: cb.query_bytes(),
          carry_hi: cb.query_bytes(),
      };

      let multiplicand_lo =
          from_bytes::expr(&gadget.multiplicand.cells[..16]);
      let multiplicand_hi =
          from_bytes::expr(&gadget.multiplicand.cells[16..]);

      let product_lo = from_bytes::expr(&gadget.product.cells[..16]);
      let product_hi = from_bytes::expr(&gadget.product.cells[16..]);

      let carry_lo = from_bytes::expr(&gadget.carry_lo[..8]);
      let carry_hi = from_bytes::expr(&gadget.carry_hi[8..]);

      cb.require_equal(
          "multiplicand_lo ⋅ multiplier == carry_lo ⋅ 2^128 + product_lo",
          multiplicand_lo * gadget.multiplier.expr(),
          carry_lo.clone() * pow_of_two_expr(128) + product_lo,
      );

      cb.require_equal(
          "multiplicand_hi ⋅ multiplier + carry_lo == carry_hi ⋅ 2^128 + product_hi",
          multiplicand_hi * gadget.multiplier.expr() + carry_lo,
          carry_hi.clone() * pow_of_two_expr(128) + product_hi,
      );

      if check_overflow {
          cb.require_zero("carry_hi == 0", carry_hi);
      }

      gadget
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      multiplicand: Word,
      multiplier: u64,
      product: Word,
  ) -> Result<(), Error> {
      self.multiplicand.assign(
          region,
          offset,
          Some(multiplicand.to_le_bytes()),
      )?;
      self.product
          .assign(region, offset, Some(product.to_le_bytes()))?;
      self.multiplier
          .assign(region, offset, Some(multiplier.into()))?;

      let (multiplicand_lo, multiplicand_hi) = split_u256(&multiplicand);
      let (product_lo, product_hi) = split_u256(&product);

      let mut assign_quotient =
          |cells: &[Cell<F>], value: Word| -> Result<(), Error> {
              for (cell, byte) in
                  cells.iter().zip(value.low_u64().to_le_bytes().iter())
              {
                  cell.assign(region, offset, Some(F::from(*byte as u64)))?;
              }
              Ok(())
          };

      let carry_lo = (multiplicand_lo * multiplier - product_lo) >> 128;
      let carry_hi =
          (multiplicand_hi * multiplier - product_hi + carry_lo) >> 128;
      assign_quotient(&self.carry_lo, carry_lo)?;
      assign_quotient(&self.carry_hi, carry_hi)?;

      Ok(())
  }

  pub(crate) fn product(&self) -> &util::Word<F> {
      &self.product
  }

  pub(crate) fn carry(&self) -> &[util::Cell<F>; 8] {
      &self.carry_hi
  }
}

/// Requires that the passed in value is within the specified range.
/// `NUM_BYTES` is required to be `<= 31`.
#[derive(Clone, Debug)]
pub struct RangeCheckGadget<F, const NUM_BYTES: usize> {
  parts: [Cell<F>; NUM_BYTES],
}

impl<F: FieldExt, const NUM_BYTES: usize> RangeCheckGadget<F, NUM_BYTES> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      value: Expression<F>,
  ) -> Self {
      assert!(NUM_BYTES <= 31, "number of bytes too large");

      let parts = cb.query_bytes();
      // Require that the reconstructed value from the parts equals the
      // original value
      cb.require_equal(
          "Constrain bytes recomposited to value",
          value,
          from_bytes::expr(&parts),
      );

      Self { parts }
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      value: F,
  ) -> Result<(), Error> {
      let bytes = value.to_bytes();
      for (idx, part) in self.parts.iter().enumerate() {
          part.assign(region, offset, Some(F::from(bytes[idx] as u64)))?;
      }
      Ok(())
  }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs `< 256**NUM_BYTES`
/// `NUM_BYTES` is required to be `<= MAX_BYTES_FIELD` to prevent overflow:
/// values are stored in a single field element and two of these
/// are added together.
/// The equation that is enforced is `lhs - rhs == diff - (lt * range)`.
/// Because all values are `<= 256**NUM_BYTES` and `lt` is boolean,
///  `lt` can only be `1` when `lhs < rhs`.
#[derive(Clone, Debug)]
pub struct LtGadget<F, const NUM_BYTES: usize> {
  lt: Cell<F>, // `1` when `lhs < rhs`, `0` otherwise.
  diff: [Cell<F>; NUM_BYTES], /* The byte values of `diff`.
                * `diff` equals `lhs - rhs` if `lhs >= rhs`,
                * `lhs - rhs + range` otherwise. */
  range: F, // The range of the inputs, `256**NUM_BYTES`
}

impl<F: FieldExt, const NUM_BYTES: usize> LtGadget<F, NUM_BYTES> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      lhs: Expression<F>,
      rhs: Expression<F>,
  ) -> Self {
      assert!(NUM_BYTES <= MAX_BYTES_FIELD, "unsupported number of bytes");

      let lt = cb.query_bool();
      let diff = cb.query_bytes();
      let range = pow_of_two(NUM_BYTES * 8);

      // The equation we require to hold: `lhs - rhs == diff - (lt * range)`.
      cb.require_equal(
          "lhs - rhs == diff - (lt ⋅ range)",
          lhs - rhs,
          from_bytes::expr(&diff) - (lt.expr() * range),
      );

      Self { lt, diff, range }
  }

  pub(crate) fn expr(&self) -> Expression<F> {
      self.lt.expr()
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      lhs: F,
      rhs: F,
  ) -> Result<(F, Vec<u8>), Error> {
      // Set `lt`
      let lt = lhs < rhs;
      self.lt.assign(
          region,
          offset,
          Some(F::from(if lt { 1 } else { 0 })),
      )?;

      // Set the bytes of diff
      let diff = (lhs - rhs) + (if lt { self.range } else { F::zero() });
      let diff_bytes = diff.to_bytes();
      for (idx, diff) in self.diff.iter().enumerate() {
          diff.assign(region, offset, Some(F::from(diff_bytes[idx] as u64)))?;
      }

      Ok((if lt { F::one() } else { F::zero() }, diff_bytes.to_vec()))
  }

  pub(crate) fn diff_bytes(&self) -> Vec<Cell<F>> {
      self.diff.to_vec()
  }
}

/// Returns (lt, eq):
/// - `lt` is `1` when `lhs < rhs`, `0` otherwise.
/// - `eq` is `1` when `lhs == rhs`, `0` otherwise.
/// lhs and rhs `< 256**NUM_BYTES`
/// `NUM_BYTES` is required to be `<= MAX_BYTES_FIELD`.
#[derive(Clone, Debug)]
pub struct ComparisonGadget<F, const NUM_BYTES: usize> {
  lt: LtGadget<F, NUM_BYTES>,
  eq: IsZeroGadget<F>,
}

impl<F: FieldExt, const NUM_BYTES: usize> ComparisonGadget<F, NUM_BYTES> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      lhs: Expression<F>,
      rhs: Expression<F>,
  ) -> Self {
      let lt = LtGadget::<F, NUM_BYTES>::construct(cb, lhs, rhs);
      let eq = IsZeroGadget::<F>::construct(cb, sum::expr(&lt.diff_bytes()));

      Self { lt, eq }
  }

  pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
      (self.lt.expr(), self.eq.expr())
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      lhs: F,
      rhs: F,
  ) -> Result<(F, F), Error> {
      // lt
      let (lt, diff) = self.lt.assign(region, offset, lhs, rhs)?;

      // eq
      let eq = self.eq.assign(region, offset, sum::value(&diff))?;

      Ok((lt, eq))
  }
}

/// Returns (is_a, is_b):
/// - `is_a` is `1` when `value == a`, else `0`
/// - `is_b` is `1` when `value == b`, else `0`
/// `value` is required to be either `a` or `b`.
/// The benefit of this gadget over `IsEqualGadget` is that the
/// expression returned is a single value which will make
/// future expressions depending on this result more efficient.
#[derive(Clone, Debug)]
pub struct PairSelectGadget<F> {
  is_a: Cell<F>,
  is_b: Expression<F>,
}

impl<F: FieldExt> PairSelectGadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      value: Expression<F>,
      a: Expression<F>,
      b: Expression<F>,
  ) -> Self {
      let is_a = cb.query_bool();
      let is_b = 1.expr() - is_a.expr();

      // Force `is_a` to be `0` when `value != a`
      cb.add_constraint(
          "is_a ⋅ (value - a)",
          is_a.expr() * (value.clone() - a),
      );
      // Force `1 - is_a` to be `0` when `value != b`
      cb.add_constraint(
          "(1 - is_a) ⋅ (value - b)",
          is_b.clone() * (value - b),
      );

      Self { is_a, is_b }
  }

  pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
      (self.is_a.expr(), self.is_b.clone())
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      value: F,
      a: F,
      _b: F,
  ) -> Result<(F, F), Error> {
      let is_a = if value == a { F::one() } else { F::zero() };
      self.is_a.assign(region, offset, Some(is_a))?;

      Ok((is_a, F::one() - is_a))
  }
}

/// Returns (quotient: numerator/divisor, remainder: numerator%divisor),
/// with `numerator` an expression and `divisor` a constant.
/// Input requirements:
/// - `quotient < 256**NUM_BYTES`
/// - `quotient * divisor < field size`
/// - `remainder < divisor` currently requires a lookup table for `divisor`
#[derive(Clone, Debug)]
pub struct ConstantDivisionGadget<F, const NUM_BYTES: usize> {
  quotient: Cell<F>,
  remainder: Cell<F>,
  divisor: u64,
  quotient_range_check: RangeCheckGadget<F, NUM_BYTES>,
}

impl<F: FieldExt, const NUM_BYTES: usize> ConstantDivisionGadget<F, NUM_BYTES> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      numerator: Expression<F>,
      divisor: u64,
  ) -> Self {
      let quotient = cb.query_cell();
      let remainder = cb.query_cell();

      // Require that remainder < divisor
      cb.range_lookup(remainder.expr(), divisor);

      // Require that quotient < 2**NUM_BYTES
      // so we can't have any overflow when doing `quotient * divisor`.
      let quotient_range_check =
          RangeCheckGadget::construct(cb, quotient.expr());

      // Check if the division was done correctly
      cb.require_equal(
          "lhnumerator - remainder == quotient ⋅ divisor",
          numerator - remainder.expr(),
          quotient.expr() * divisor.expr(),
      );

      Self {
          quotient,
          remainder,
          divisor,
          quotient_range_check,
      }
  }

  pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
      // Return the quotient and the remainder
      (self.quotient.expr(), self.remainder.expr())
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      numerator: u128,
  ) -> Result<(u128, u128), Error> {
      let divisor = self.divisor as u128;
      let quotient = numerator / divisor;
      let remainder = numerator % divisor;
      self.quotient
          .assign(region, offset, Some(F::from_u128(quotient)))?;
      self.remainder
          .assign(region, offset, Some(F::from_u128(remainder)))?;

      self.quotient_range_check.assign(
          region,
          offset,
          F::from_u128(quotient),
      )?;

      Ok((quotient, remainder))
  }
}

/// Returns `rhs` when `lhs < rhs`, and returns `lhs` otherwise.
/// lhs and rhs `< 256**NUM_BYTES`
/// `NUM_BYTES` is required to be `<= 31`.
#[derive(Clone, Debug)]
pub struct MaxGadget<F, const NUM_BYTES: usize> {
  lt: LtGadget<F, NUM_BYTES>,
  max: Expression<F>,
}

impl<F: FieldExt, const NUM_BYTES: usize> MaxGadget<F, NUM_BYTES> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      lhs: Expression<F>,
      rhs: Expression<F>,
  ) -> Self {
      let lt = LtGadget::construct(cb, lhs.clone(), rhs.clone());
      let max = select::expr(lt.expr(), rhs, lhs);

      Self { lt, max }
  }

  pub(crate) fn expr(&self) -> Expression<F> {
      self.max.clone()
  }

  pub(crate) fn assign(
      &self,
      region: &mut Region<'_, F>,
      offset: usize,
      lhs: F,
      rhs: F,
  ) -> Result<F, Error> {
      let (lt, _) = self.lt.assign(region, offset, lhs, rhs)?;
      Ok(select::value(lt, rhs, lhs))
  }
}

//generating Lagrange base polynomial for a cell.
//the polynomial will equal to 1 when cell equals to idx, otherwise 0.
//the cell's domain will be 0..domain_size
fn generate_lagrange_base_polynomial<F: FieldExt>(
  cell: Cell<F>,
  idx: u64,
  domain_size: u64,
) -> Expression<F> {
  let mut base_ploy = 1.expr();
  let mut accumulated_inverse = 1.expr();
  for x in 0..domain_size {
      if x != idx {
          base_ploy = base_ploy * (cell.expr() - x.expr());
          let inverse = if x < idx {
              F::from_u128((idx - x) as u128).invert().unwrap()
          } else {
              -F::from_u128((x - idx) as u128).invert().unwrap()
          };
          accumulated_inverse = accumulated_inverse * inverse;
      }
  }
  base_ploy * accumulated_inverse
}

#[derive(Clone, Debug)]
pub struct SarWordsGadget<F> {
    // * input和output
    a: util::Word<F>,
    shift: util::Word<F>,
    b: util::Word<F>,
    // * 拆分的high和low数据
    a_slice_front: [Cell<F>; 32],
    a_slice_back: [Cell<F>; 32],
    // * 进行中间计算的字段，详见markdown
    shift_div_by_64: Cell<F>,
    shift_mod_by_64_div_by_8: Cell<F>,
    shift_mod_by_64_decpow: Cell<F>, // means 2^(8-shift_mod_by_64)
    shift_mod_by_64_pow: Cell<F>,    // means 2^shift_mod_by_64
    shift_mod_by_8: Cell<F>,
    // * 判断是否为负数 -> SAR负数 top bit为1
    is_neg: Cell<F>,
}
impl<F: FieldExt> SarWordsGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        a: util::Word<F>,
        shift: util::Word<F>,
    ) -> Self {
        // * query_word
        let b = cb.query_word();
        // * query_byte
        let a_slice_front = array_init::array_init(|_| cb.query_byte());
        let a_slice_back = array_init::array_init(|_| cb.query_byte());
        // * query_cell
        let shift_div_by_64 = cb.query_cell();
        let shift_mod_by_64_div_by_8 = cb.query_cell();
        let shift_mod_by_64_decpow = cb.query_cell();
        let shift_mod_by_64_pow = cb.query_cell();
        let shift_mod_by_8 = cb.query_cell();
        // * query_bool
        let is_neg = cb.query_bool();

        // rename variable:
        // shift_div_by_64 :a
        // shift_mod_by_64_div_by_8:b
        // shift_mod_by_8:c
        // we split shift to the equation:
        // shift == a * 64 + b * 8 + c
        let shift_mod_by_64 =
            // * b * 8 + c
            8.expr() * shift_mod_by_64_div_by_8.expr() + shift_mod_by_8.expr();
        cb.require_equal(
            // * shift == a * 64 + b * 8 + c
            "shift == shift_div_by_64 * 64 + shift_mod_by_64_div_by_8 * 8 + shift_mod_by_8",
            shift.expr(),
            shift_div_by_64.expr() * 64.expr() + shift_mod_by_64.clone(),
        );

        // * 低n位放到back
        // * 高64-n位放到front
        // merge 8 8-bit cell for a 64-bit expression
        // for a, a_slice_front, a_slice_back, b
        let mut a_digits = vec![];
        let mut a_slice_front_digits = vec![];
        let mut a_slice_back_digits = vec![];
        let mut b_digits = vec![];
        // * 拆成四个limbs
        for virtual_idx in 0..4 {
            // * 第1对：0 ... 8
            // * 第2对：9 ... 16
            // * 第3对：17 ... 24
            // * 第4对：25 ... 32 -> 32个cell（每个cell是1byte），1byte = 8bit
            let now_idx = (virtual_idx * 8) as usize;
            a_digits.push(from_bytes::expr(&a.cells[now_idx..now_idx + 8]));
            // * 把256-bit的low都放到back、high都放到front
            a_slice_back_digits
                .push(from_bytes::expr(&a_slice_back[now_idx..now_idx + 8]));
            a_slice_front_digits
                .push(from_bytes::expr(&a_slice_front[now_idx..now_idx + 8]));
            // * 这个应该是shift完成之后的新word -> b
            b_digits.push(from_bytes::expr(&b.cells[now_idx..now_idx + 8]));
        }

        // * 应该是2^64
        let radix_constant_64 = pow_of_two_expr(64);
        let neg_high_constant =
            radix_constant_64.clone() - shift_mod_by_64_decpow.expr();
        let neg_constant = radix_constant_64 - 1.expr();
        let mut sar_constraints =
            (0..4).map(|_| 0.expr()).collect::<Vec<Expression<F>>>();
        for transplacement in (0_usize)..(4_usize) {
            // generate the polynomial depends on the shift_div_by_64
            let select_transplacement_polynomial =
                // * 之后我们会尝试直接在这里调用函数 -> 看看是否会error
                // * 参数都不一样，需要重新调用这个function（预计会是一个比较棘手的地方）
                // ! 这里有一定的不兼容风险
                generate_lagrange_base_polynomial(
                    shift_div_by_64.clone(),
                    transplacement as u64,
                    4u64,
                );
            for idx in 0..(4 - transplacement) {
                let tmpidx = idx + transplacement;
                let merge_a = if idx + transplacement == (3_usize) {
                    a_slice_front_digits[tmpidx].clone()
                        + is_neg.expr() * neg_high_constant.clone()
                } else {
                    a_slice_front_digits[tmpidx].clone()
                        + a_slice_back_digits[tmpidx + 1].clone()
                            * shift_mod_by_64_decpow.expr()
                };
                sar_constraints[idx] = sar_constraints[idx].clone()
                    + select_transplacement_polynomial.clone()
                        * (merge_a - b_digits[idx].clone());
            }
            for idx in (4 - transplacement)..4 {
                sar_constraints[idx] = sar_constraints[idx].clone()
                    + select_transplacement_polynomial.clone()
                        * (b_digits[idx].clone()
                            - is_neg.expr() * neg_constant.clone());
            }
        }
        (0..4).for_each(|idx|
            cb.require_zero(
                "merge a_slice_back_digits and a_slice_front_digits == b_digits",
                sar_constraints[idx].clone(),
            )
        );

        // for i in 0..4
        // a_slice_back_digits[i] + a_slice_front_digits * shift_mod_by_64_pow
        // == a_digits[i]
        for idx in 0..4 {
            cb.require_equal(
                // * 检查这个约束关系
                "a[idx] == a_slice_back[idx] + a_slice_front[idx] * shift_mod_by_64_pow",
                a_slice_back_digits[idx].clone() + a_slice_front_digits[idx].clone() * shift_mod_by_64_pow.expr(),
                a_digits[idx].clone(),
            );
        }

        // check serveral higher cells == 0 for slice_back and slice_front
        let mut equal_to_zero = 0.expr();
        for digit_transplacement in 0..8 {
            let select_transplacement_polynomial =
                // ! 这里有一定的不兼容风险
                generate_lagrange_base_polynomial(
                    shift_mod_by_64_div_by_8.clone(),
                    digit_transplacement as u64,
                    8u64,
                );
            // * front和back
            for virtual_idx in 0..4 {
                for idx in (digit_transplacement + 1)..8 {
                    let nowidx = (virtual_idx * 8 + idx) as usize;
                    equal_to_zero = equal_to_zero
                        + (select_transplacement_polynomial.clone()
                            * a_slice_back[nowidx].expr());
                }
                for idx in (8 - digit_transplacement)..8 {
                    let nowidx = (virtual_idx * 8 + idx) as usize;
                    equal_to_zero = equal_to_zero
                        + (select_transplacement_polynomial.clone()
                            * a_slice_front[nowidx].expr());
                }
            }
        }
        // for i in 1..32
        // check shift[i] == 0
        for idx in 1..32 {
            // * equal_to_zero就是`0.expr()`
            // * 检查shift[i] == 0的约束关系
            equal_to_zero = equal_to_zero + shift.cells[idx].expr();
        }
        cb.require_zero(
            "several higher part of slice should be zero.",
            equal_to_zero,
        );

        //check the specific 4 cells in 0..(1 << shift_mod_by_8).
        //check another specific 4 cells in 0..(1 << (8 - shift_mod_by_8)).
        for virtual_idx in 0..4 {
            let mut slice_bits_polynomial = vec![0.expr(), 0.expr()];
            for digit_transplacement in 0..8 {
                let select_transplacement_polynomial =
                    // ! 这里有一定的不兼容风险
                    generate_lagrange_base_polynomial(
                        shift_mod_by_64_div_by_8.clone(),
                        digit_transplacement as u64,
                        8u64,
                    );
                let nowidx = (virtual_idx * 8 + digit_transplacement) as usize;
                slice_bits_polynomial[0] = slice_bits_polynomial[0].clone()
                    + select_transplacement_polynomial.clone()
                        * a_slice_back[nowidx].expr();
                let nowidx =
                    (virtual_idx * 8 + 7 - digit_transplacement) as usize;
                slice_bits_polynomial[1] = slice_bits_polynomial[1].clone()
                    + select_transplacement_polynomial.clone()
                        * a_slice_front[nowidx].expr();
            }
            cb.add_lookup(Lookup::Fixed {
                tag: FixedTableTag::Bitslevel.expr(),
                values: [
                    shift_mod_by_8.expr(),
                    slice_bits_polynomial[0].clone(),
                    0.expr(),
                ],
            });
            cb.add_lookup(Lookup::Fixed {
                tag: FixedTableTag::Bitslevel.expr(),
                values: [
                    8.expr() - shift_mod_by_8.expr(),
                    slice_bits_polynomial[1].clone(),
                    0.expr(),
                ],
            });
        }

        // check:
        // 2^shift_mod_by_64 == shift_mod_by_64_pow
        // 2^(8-shift_mod_by_64) == shift_mod_by_64_decpow
        cb.add_lookup(Lookup::Fixed {
            tag: FixedTableTag::Pow64.expr(),
            values: [
                shift_mod_by_64,
                shift_mod_by_64_pow.expr(),
                shift_mod_by_64_decpow.expr(),
            ],
        });

        cb.add_lookup(Lookup::Fixed {
            tag: FixedTableTag::Bitslevel.expr(),
            values: [2.expr(), shift_div_by_64.expr(), 0.expr()],
        });
        cb.add_lookup(Lookup::Fixed {
            tag: FixedTableTag::Bitslevel.expr(),
            values: [3.expr(), shift_mod_by_64_div_by_8.expr(), 0.expr()],
        });
        cb.add_lookup(Lookup::Fixed {
            tag: FixedTableTag::Bitslevel.expr(),
            values: [3.expr(), shift_mod_by_8.expr(), 0.expr()],
        });

        // * 返回的约束用来做assign
        Self {
            a,
            shift,
            b,
            a_slice_front,
            a_slice_back,
            shift_div_by_64,
            shift_mod_by_64_div_by_8,
            shift_mod_by_64_decpow,
            shift_mod_by_64_pow,
            shift_mod_by_8,
            is_neg,
        }
    }
    
    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        a: Word,
        shift: Word,
        b: Word,
    ) -> Result<(), Error> {
      self.assign_witness(region, offset, &a, &shift)?;
      self.a.assign(region, offset, Some(a.to_le_bytes()))?;
      self.shift
          .assign(region, offset, Some(shift.to_le_bytes()))?;
      self.b.assign(region, offset, Some(b.to_le_bytes()))?;
      Ok(())
  }

    pub(crate) fn b(&self) -> &util::Word<F> {
        &self.b
    }

    fn assign_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        wa: &Word,
        wshift: &Word,
    ) -> Result<(), Error> {
      let a8s = wa.to_le_bytes();
      let is_neg = a8s[31] >= 128;
      let shift = wshift.to_le_bytes()[0] as u128;
      let shift_div_by_64 = shift / 64;
      let shift_mod_by_64_div_by_8 = shift % 64 / 8;
      let shift_mod_by_64 = shift % 64;
      let shift_mod_by_64_pow = 1u128 << shift_mod_by_64;
      let shift_mod_by_64_decpow =
          (1u128 << 64) / (shift_mod_by_64_pow as u128);
      let shift_mod_by_8 = shift % 8;
      let mut a_slice_front = [0u8; 32];
      let mut a_slice_back = [0u8; 32];
      for virtual_idx in 0..4 {
          let mut tmp_a: u64 = 0;
          for idx in 0..8 {
              let now_idx = virtual_idx * 8 + idx;
              tmp_a += (1u64 << (8 * idx)) * (a8s[now_idx] as u64);
          }
          let mut slice_back = if shift_mod_by_64 == 0 {
              0
          } else {
              tmp_a % (1u64 << shift_mod_by_64)
          };
          let mut slice_front = if shift_mod_by_64 == 0 {
              tmp_a
          } else {
              tmp_a / (1u64 << shift_mod_by_64)
          };
          for idx in 0..8 {
              let now_idx = virtual_idx * 8 + idx;
              a_slice_back[now_idx] = (slice_back % (1 << 8)) as u8;
              a_slice_front[now_idx] = (slice_front % (1 << 8)) as u8;
              slice_back >>= 8;
              slice_front >>= 8;
          }
      }
      a_slice_front
          .iter()
          .zip(self.a_slice_front.iter())
          .try_for_each(|(bt, assignee)| -> Result<(), Error> {
              assignee.assign(region, offset, Some(F::from(*bt as u64)))?;
              Ok(())
          })?;
      a_slice_back
          .iter()
          .zip(self.a_slice_back.iter())
          .try_for_each(|(bt, assignee)| -> Result<(), Error> {
              assignee.assign(region, offset, Some(F::from(*bt as u64)))?;
              Ok(())
          })?;
      self.shift_div_by_64.assign(
          region,
          offset,
          Some(F::from_u128(shift_div_by_64)),
      )?;
      self.shift_mod_by_64_div_by_8.assign(
          region,
          offset,
          Some(F::from_u128(shift_mod_by_64_div_by_8)),
      )?;
      self.shift_mod_by_64_decpow.assign(
          region,
          offset,
          Some(F::from_u128(shift_mod_by_64_decpow)),
      )?;
      self.shift_mod_by_64_pow.assign(
          region,
          offset,
          Some(F::from_u128(shift_mod_by_64_pow)),
      )?;
      self.shift_mod_by_8.assign(
          region,
          offset,
          Some(F::from_u128(shift_mod_by_8)),
      )?;
      self.is_neg
          .assign(region, offset, Some(F::from(is_neg as u64)))?;

      Ok(())
  }
}
