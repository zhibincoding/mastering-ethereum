use ff::Field;
use group::Curve;

// 访问父模块的私有功能，所以这里的argument、pk、vk都会调用这个keygen.rs
use super::{Argument, ProvingKey, VerifyingKey};
// 绝对路径引入模块
use crate::{
    // arithmetic主要就是一些common的工具（struct、trait等等）
    // for group, field and polynomial arithmetic
    // 1）CurveAffine(trait): This trait is the affine counterpart to Curve and is used for serialization, storage in memory, and inspection of x and y coordinates
    // affine curarure: https://en.wikipedia.org/wiki/Affine_curvature
    // 2）FieldExt(trait): 一些处理finite field上elements的common interface
    arithmetic::{CurveAffine, FieldExt},
    // 这个库是Plonk的实现，但是pse把IPA换成了KZG（可能因为暂时不需要递归证明，减少overhead等原因）
    // 1）Any(enums): advice、fixed、instance columns
    // 2）Column(struct) -> 传入index和type，暂不清楚更具体的作用
    // 3）Error -> proving 或者 circuit synthesis的时候可能会出现的错误
    plonk::{Any, Column, Error},
    // poly相关的各种工具 -> Contains utilities for performing arithmetic over univariate polynomials in various forms, 
    // including computing commitments to them and provably opening the committed polynomials at arbitrary points
    // 1）commitment(module) -> Halo2用的polynomial commitment scheme，PSE换回KZG的时候，估计操作的就是这个模块
    // Build(struct) -> Wrapper type around a blinding factor
    // Params(struct) -> Polynomial commitment scheme的public input
    // 2）EvaluationDomain(struct) -> 顾名思义，主要做polynomial evaluation
    poly::{
        commitment::{Blind, Params},
        EvaluationDomain,
    },
};
#[derive(Debug)]
pub(crate) struct Assembly {
    columns: Vec<Column<Any>>,
    pub(crate) mapping: Vec<Vec<(usize, usize)>>,
    aux: Vec<Vec<(usize, usize)>>,
    sizes: Vec<Vec<usize>>,
}

impl Assembly {
    pub(crate) fn new(n: usize, p: &Argument) -> Self {
        // Initialize the copy vector to keep track of copy constraints in all
        // the permutation arguments.
        let mut columns = vec![];
        for i in 0..p.columns.len() {
            // Computes [(i, 0), (i, 1), ..., (i, n - 1)]
            columns.push((0..n).map(|j| (i, j)).collect());
        }

        // Before any equality constraints are applied, every cell in the permutation is
        // in a 1-cycle; therefore mapping and aux are identical, because every cell is
        // its own distinguished element.
        Assembly {
            columns: p.columns.clone(),
            mapping: columns.clone(),
            aux: columns,
            sizes: vec![vec![1usize; n]; p.columns.len()],
        }
    }

    pub(crate) fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        let left_column = self
            .columns
            .iter()
            .position(|c| c == &left_column)
            .ok_or(Error::ColumnNotInPermutation(left_column))?;
        let right_column = self
            .columns
            .iter()
            .position(|c| c == &right_column)
            .ok_or(Error::ColumnNotInPermutation(right_column))?;

        // Check bounds
        if left_row >= self.mapping[left_column].len()
            || right_row >= self.mapping[right_column].len()
        {
            return Err(Error::BoundsFailure);
        }

        // See book/src/design/permutation.md for a description of this algorithm.

        let mut left_cycle = self.aux[left_column][left_row];
        let mut right_cycle = self.aux[right_column][right_row];

        // If left and right are in the same cycle, do nothing.
        if left_cycle == right_cycle {
            return Ok(());
        }

        if self.sizes[left_cycle.0][left_cycle.1] < self.sizes[right_cycle.0][right_cycle.1] {
            std::mem::swap(&mut left_cycle, &mut right_cycle);
        }

        // Merge the right cycle into the left one.
        self.sizes[left_cycle.0][left_cycle.1] += self.sizes[right_cycle.0][right_cycle.1];
        let mut i = right_cycle;
        loop {
            self.aux[i.0][i.1] = left_cycle;
            i = self.mapping[i.0][i.1];
            if i == right_cycle {
                break;
            }
        }

        let tmp = self.mapping[left_column][left_row];
        self.mapping[left_column][left_row] = self.mapping[right_column][right_row];
        self.mapping[right_column][right_row] = tmp;

        Ok(())
    }

    pub(crate) fn build_vk<C: CurveAffine>(
        self,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        p: &Argument,
    ) -> VerifyingKey<C> {
        // * 参考 Halo2 protocol
        // * 这里是prover algorithm中的commit for permutation polynomial（4.）
        // * Compute [omega^0, omega^1, ..., omega^{params.n - 1}]

        // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
        let mut omega_powers = Vec::with_capacity(params.n as usize);
        {
            let mut cur = C::Scalar::one();
            for _ in 0..params.n {
                omega_powers.push(cur);
                cur *= &domain.get_omega();
            }
        }

        // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
        let mut deltaomega = Vec::with_capacity(p.columns.len());
        {
            let mut cur = C::Scalar::one();
            for _ in 0..p.columns.len() {
                let mut omega_powers = omega_powers.clone();
                for o in &mut omega_powers {
                    *o *= &cur;
                }

                deltaomega.push(omega_powers);

                cur *= &C::Scalar::DELTA;
            }
        }

        // Pre-compute commitments for the URS.
        let mut commitments = vec![];
        for i in 0..p.columns.len() {
            // Computes the permutation polynomial based on the permutation
            // description in the assembly.
            let mut permutation_poly = domain.empty_lagrange();
            for (j, p) in permutation_poly.iter_mut().enumerate() {
                let (permuted_i, permuted_j) = self.mapping[i][j];
                *p = deltaomega[permuted_i][permuted_j];
            }

            // Compute commitment to permutation polynomial
            commitments.push(params.commit_lagrange(&permutation_poly).to_affine());
        }
        VerifyingKey { commitments }
    }

    pub(crate) fn build_pk<C: CurveAffine>(
        self,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        p: &Argument,
    ) -> ProvingKey<C> {
        // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
        let mut omega_powers = Vec::with_capacity(params.n as usize);
        {
            let mut cur = C::Scalar::one();
            for _ in 0..params.n {
                omega_powers.push(cur);
                cur *= &domain.get_omega();
            }
        }

        // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
        let mut deltaomega = Vec::with_capacity(p.columns.len());
        {
            let mut cur = C::Scalar::one();
            for _ in 0..p.columns.len() {
                let mut omega_powers = omega_powers.clone();
                for o in &mut omega_powers {
                    *o *= &cur;
                }

                deltaomega.push(omega_powers);

                cur *= &C::Scalar::DELTA;
            }
        }

        // Compute permutation polynomials, convert to coset form.
        let mut permutations = vec![];
        let mut polys = vec![];
        let mut cosets = vec![];
        for i in 0..p.columns.len() {
            // Computes the permutation polynomial based on the permutation
            // description in the assembly.
            let mut permutation_poly = domain.empty_lagrange();
            for (j, p) in permutation_poly.iter_mut().enumerate() {
                let (permuted_i, permuted_j) = self.mapping[i][j];
                *p = deltaomega[permuted_i][permuted_j];
            }

            // Store permutation polynomial and precompute its coset evaluation
            permutations.push(permutation_poly.clone());
            let poly = domain.lagrange_to_coeff(permutation_poly);
            polys.push(poly.clone());
            cosets.push(domain.coeff_to_extended(poly));
        }
        ProvingKey {
            permutations,
            polys,
            cosets,
        }
    }
}