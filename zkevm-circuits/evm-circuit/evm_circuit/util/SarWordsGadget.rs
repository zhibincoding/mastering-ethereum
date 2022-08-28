// ! Draft -> 古版本的SarWordsGadget，方便我们后面对照修改

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
  a: util::Word<F>,
  shift: util::Word<F>,
  b: util::Word<F>,
  a_slice_front: [Cell<F>; 32],
  a_slice_back: [Cell<F>; 32],
  shift_div_by_64: Cell<F>,
  shift_mod_by_64_div_by_8: Cell<F>,
  shift_mod_by_64_decpow: Cell<F>, // means 2^(8-shift_mod_by_64)
  shift_mod_by_64_pow: Cell<F>,    // means 2^shift_mod_by_64
  shift_mod_by_8: Cell<F>,
  is_neg: Cell<F>,
}
impl<F: FieldExt> SarWordsGadget<F> {
  pub(crate) fn construct(
      cb: &mut ConstraintBuilder<F>,
      a: util::Word<F>,
      shift: util::Word<F>,
  ) -> Self {
      let b = cb.query_word();
      let a_slice_front = array_init::array_init(|_| cb.query_byte());
      let a_slice_back = array_init::array_init(|_| cb.query_byte());
      let shift_div_by_64 = cb.query_cell();
      let shift_mod_by_64_div_by_8 = cb.query_cell();
      let shift_mod_by_64_decpow = cb.query_cell();
      let shift_mod_by_64_pow = cb.query_cell();
      let shift_mod_by_8 = cb.query_cell();
      let is_neg = cb.query_bool();

      // rename variable:
      // shift_div_by_64 :a
      // shift_mod_by_64_div_by_8:b
      // shift_mod_by_8:c
      // we split shift to the equation:
      // shift == a * 64 + b * 8 + c
      let shift_mod_by_64 =
          8.expr() * shift_mod_by_64_div_by_8.expr() + shift_mod_by_8.expr();
      cb.require_equal(
          "shift == shift_div_by_64 * 64 + shift_mod_by_64_div_by_8 * 8 + shift_mod_by_8",
          shift.expr(),
          shift_div_by_64.expr() * 64.expr() + shift_mod_by_64.clone(),
      );

      // merge 8 8-bit cell for a 64-bit expression
      // for a, a_slice_front, a_slice_back, b
      let mut a_digits = vec![];
      let mut a_slice_front_digits = vec![];
      let mut a_slice_back_digits = vec![];
      let mut b_digits = vec![];
      for virtual_idx in 0..4 {
          let now_idx = (virtual_idx * 8) as usize;
          a_digits.push(from_bytes::expr(&a.cells[now_idx..now_idx + 8]));
          a_slice_back_digits
              .push(from_bytes::expr(&a_slice_back[now_idx..now_idx + 8]));
          a_slice_front_digits
              .push(from_bytes::expr(&a_slice_front[now_idx..now_idx + 8]));
          b_digits.push(from_bytes::expr(&b.cells[now_idx..now_idx + 8]));
      }

      let radix_constant_64 = pow_of_two_expr(64);
      let neg_high_constant =
          radix_constant_64.clone() - shift_mod_by_64_decpow.expr();
      let neg_constant = radix_constant_64 - 1.expr();
      let mut sar_constraints =
          (0..4).map(|_| 0.expr()).collect::<Vec<Expression<F>>>();
      for transplacement in (0_usize)..(4_usize) {
          // generate the polynomial depends on the shift_div_by_64
          let select_transplacement_polynomial =
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
              "a[idx] == a_slice_back[idx] + a_slice_front[idx] * shift_mod_by_64_pow",
              a_slice_back_digits[idx].clone() + a_slice_front_digits[idx].clone() * shift_mod_by_64_pow.expr(),
              a_digits[idx].clone(),
          );
      }

      // check serveral higher cells == 0 for slice_back and slice_front
      let mut equal_to_zero = 0.expr();
      for digit_transplacement in 0..8 {
          let select_transplacement_polynomial =
              generate_lagrange_base_polynomial(
                  shift_mod_by_64_div_by_8.clone(),
                  digit_transplacement as u64,
                  8u64,
              );
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