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

        // 1）在创建vector的时候，指定一个足够大的容量值，尽可能减少内存拷贝(就是避免后面vec不够大)
        // params是一个struct，里面有k n g等，是polynomial commitment scheme上的东西
        // usize是指针大小的。在32位计算机上就是u32，在64位计算机上就是u64
        let mut omega_powers = Vec::with_capacity(params.n as usize);
        {
            // 2）C是CurveAffine，就是作用域相关的一些东西
            // Scalar可以是field上的某一个element（当前context，也跟vector[向量] space有关）
            // one：Returns the one element of the field, the multiplicative identity
            // 总的来说就是返回作用域上的一个数字
            let mut cur = C::Scalar::one();
            // 3）这里的n应该是params的长度（capacity）
            for _ in 0..params.n {
                // 4）往vec中push值进去
                // 数学上应该是拿到omega，然后计算omega^0 ... omega^n-1，最后push到cur里
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

#[test]
fn run_new_parallelize() {
    // * 知道a和b，把它们element位的加起来
    // * 我感觉要写一个新的数组c，然后每一位(0 1 2 3)都把a和b对应位的数字加起来

    let mut a:Vec<i32> = (0..80).collect();
    let b:Vec<i32> = (0..80).collect();
    let mut c = vec![0; 80];

    // 0 - 10, start = 0
    // 10 - 20, satrt = 10
    // ...
    // 70 - 80, start = 70

    parallelize(&mut c, |c, start| {    // ! 改到80的时候，才出现多线程：0 10 20 .. 70
        // println!("{}", start); // 0 10 20 .. 70
        // @ 每次跑完一段thread之后，都重新赋值a和b（因为c的长度只有10）

        for i in 0..c.len() { // @ 这里的c已经是子数组了，所以每一段只有10的长度
            // ! 第一个thread（0-10）、第二个thread（10-20）
            // ! i都从0到10

            // ! 第一个thread操作的是a[0..10]、b[0..10]
            // ! 第二个thread操作的是a[10..20]、b[10..20]
            c[i] = a[start + i] + b[start + i];
        }
    });

    println!("{:?}", c);

}

#[test]
fn run_itermut_parallelize() {
    // * 知道a和b，把它们element位的加起来
    // * 我感觉要写一个新的数组c，然后每一位(0 1 2 3)都把a和b对应位的数字加起来

    let mut a:Vec<i32> = (0..80).collect();
    let mut b:Vec<i32> = (0..80).collect();
    let mut c = vec![0; 80];

    parallelize(&mut c, |c, start| {    // ! 改到80的时候，才出现多线程：0 10 20 .. 70
        // println!("{}", start); // 0 10 20 .. 70
        // @ 每次跑完一段thread之后，都重新赋值a和b（因为c的长度只有10）

        for (i, v) in c.iter_mut().enumerate() { // @ 这里的c已经是子数组了，所以每一段只有10的长度
            // ! 循环c里面的每一个元素
            // @ 这里要解引用，才能把a和b的值给v
            // @ 直接操作v就可以，v会把值返回给scope外的c
            *v = a[start + i] + b[start + i];
        }
    });

    println!("{:?}", c);
}