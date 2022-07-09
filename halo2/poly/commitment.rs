//! This module contains an implementation of the polynomial commitment scheme
//! described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use super::{Coeff, LagrangeCoeff, Polynomial, MSM};
use crate::arithmetic::{
    best_fft, best_multiexp, parallelize, CurveAffine, CurveExt, Engine, FieldExt, Group,
};
use crate::helpers::CurveRead;

use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve, Group as _, GroupEncoding};
use rand_core::OsRng;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign};

use std::io;

/// These are the prover parameters for the polynomial commitment scheme.
// * prover的参数，也就是在setup生成pk vk的params，如果泄露有安全风险 ->（伪造pk vk和proof）
// * 传入到keygen.rs生成vk的params，貌似是prover对polynomial commitment需要的参数
#[derive(Debug)]
pub struct Params<C: CurveAffine> {
    pub(crate) k: u32,
    // 就在这里
    pub(crate) n: u64,
    // 这里定义了g和g_l的类型
    pub(crate) g: Vec<C>,
    pub(crate) g_lagrange: Vec<C>,
    pub(crate) additional_data: Vec<u8>,
}

/// These are the verifier parameters for the polynomial commitment scheme.
/// 上面是prover的部分，下面是verifier的部分
#[derive(Debug)]
pub struct ParamsVerifier<E: Engine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g1: E::G1Affine,
    pub(crate) g2: E::G2Affine,
    pub(crate) s_g2: E::G2Affine,
    pub(crate) g_lagrange: Vec<E::G1Affine>,
}

#[cfg(test)]
mod tests {
    use pairing::arithmetic::CurveAffine;

    use super::Params;

    impl<C: CurveAffine> Params<C> {
        pub fn do_this() {}
    }
}

// * δ = (G, F_p, **G**, H)
// * Commit(δ, p(X); r)
impl<C: CurveAffine> Params<C> {
    /// Initializes parameters for the curve, Draws random toxic point inside of the function
    /// MUST NOT be used in production
    /// 
    /// 这里的setup是不太安全的，所以不能用于生产环境
    pub fn unsafe_setup<E: Engine>(k: u32) -> Params<E::G1Affine> {
        // TODO: Make this function only available in test mod
        // Largest root of unity exponent of the Engine is `2^E::Scalar::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Scalar::S`.
        assert!(k <= E::Scalar::S);
        let n: u64 = 1 << k;

        // * 原本是一个顺序实现，每个位置都是一个幂次
        // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
        let g1 = <E::G1Affine as PrimeCurveAffine>::generator();
        let s = E::Scalar::random(OsRng);


        // !原来的实现
        // let mut g_projective: Vec<E::G1> = Vec::with_capacity(n as usize);
        // let g1 = <E::G1Affine as PrimeCurveAffine>::generator();
        // g_projective.push(g1.into());
        // // g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1]
        // for i in 1..(n as usize) {
        //     // 这里的s在上面定义，这个很长的字段里面每个元素都 * s
        //     g_projective.push(g_projective[i - 1] * s);
        // }



        let mut g_projective = vec![E::G1::group_zero(); n as usize];
        // * 这是tianyi的另一个优化，把很长的g_projective，拆分成了好几段
        // * 每一段都调用后面的f函数 -> 所以我们拆没有问题，调用的函数有点问题

        // * 这里应该是 f:|g,start|，但是我们的插件没表示出来
        // * g是字段，start是offset
        parallelize(&mut g_projective, |g, start| {
            let mut current_g: E::G1 = g1.into();
            // * start是这个字段的index
            // * 这里计算 G1, [s]G1, [s^2]G1 ...
            // pow_vartime应该就是进行幂运算，start从0到n-1 [s^0] [s^1] [s^2] ...
            // current_g *=再自乘g，就是 G1, [s]G1, [s^2]G1 ...
            current_g *= s.pow_vartime(&[start as u64]);
            // * iter_mut相当于得到一个指针（?什么意思），可以修改g的值
            for g in g.iter_mut() {
                // 让第一个g变成current_g
                *g = current_g;
                // 自乘 current_g = current_g * s，这里的s是什么
                current_g *= s;
            }
            // * 第二次循环，g被赋值为一个乘过s的current_g
            // * [current_g, current_g*s, (current_g*s)*s ]
            // * [G, [s]G, [s^2]G]
        });

        let g = {
            let mut g = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                E::G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g
        };

        let mut g_lagrange_projective = vec![E::G1::group_zero(); n as usize];
        let mut root = E::Scalar::ROOT_OF_UNITY_INV.invert().unwrap();
        for _ in k..E::Scalar::S {
            root = root.square();
        }
        let n_inv = Option::<E::Scalar>::from(E::Scalar::from(n).invert())
            .expect("inversion should be ok for n = 1<<k");
        let multiplier = (s.pow_vartime(&[n as u64]) - E::Scalar::one()) * n_inv;
        parallelize(&mut g_lagrange_projective, |g, start| {
            for (idx, g) in g.iter_mut().enumerate() {
                let offset = start + idx;
                let root_pow = root.pow_vartime(&[offset as u64]);
                let scalar = multiplier * root_pow * (s - root_pow).invert().unwrap();
                *g = g1 * scalar;
            }
        });

        let g_lagrange = {
            let mut g_lagrange = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g_lagrange, |g_lagrange, starts| {
                E::G1::batch_normalize(
                    &g_lagrange_projective[starts..(starts + g_lagrange.len())],
                    g_lagrange,
                );
            });
            drop(g_lagrange_projective);
            g_lagrange
        };

        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let s_g2 = g2 * s;
        let additional_data = Vec::from(s_g2.to_bytes().as_ref());
        Params {
            k,
            n,
            g,
            g_lagrange,
            additional_data,
        }
    }

    /// This computes a commitment to a polynomial described by the provided
    /// slice of coefficients. The commitment will be blinded by the blinding
    /// factor `r`.
    pub fn commit(&self, poly: &Polynomial<C::Scalar, Coeff>) -> C::Curve {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// This commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain. The commitment will be blinded by the blinding factor
    /// `r`.
    pub fn commit_lagrange(&self, poly: &Polynomial<C::Scalar, LagrangeCoeff>) -> C::Curve {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<C> {
        MSM::new()
    }

    /// Getter for g generators
    pub fn get_g(&self) -> Vec<C> {
        self.g.clone()
    }

    /// Writes params to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        for el in &self.g {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        for el in &self.g_lagrange {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        let additional_data_len = self.additional_data.len() as u32;
        writer.write_all(&additional_data_len.to_le_bytes())?;
        writer.write_all(&self.additional_data)?;
        Ok(())
    }

    // * zkp的随机数很有可能来源于计算机硬件（computer buffer）
    // * 模拟电子运动，创造出物理世界的真随机数，就在buffer的位置吗？存疑

    /// Reads params from a buffer.
    /// 
    /// 这个函数只有一个参数，就是reader
    pub fn read<R: io::Read>(mut reader: R) -> io::Result<Self> {
        // 创建了[0, 0, 0, 0]这样的array，而且元素的类型都是u8，刚好符合read_exact的参数类型
        let mut k = [0u8; 4];
        // reader是什么东西，到底传入什么
        // reader确定多少个byte才能填满k
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        // a << k 相当于 a.shl(b)
        // n这个数字后面会变得非常大
        let n = 1 << k;

        // * 之前的代码
        // * 主要定义g和g_lagrange（好奇为什么这里的数据完全一致）
        // * 主要作用就是把0..n的数据都填进去，而且保证是vector（collection）的格式

        // let g: Vec<C> = (0..n)
        //     .map(|_| C::read(&mut reader))
        //     .collect::<Result<_, _>>()?;
        // let g_lagrange: Vec<C> = (0..n)
        //     .map(|_| C::read(&mut reader))
        //     .collect::<Result<_, _>>()?;

        // !从这里开始
        // 这里的reader不出意外应该就是file，里面存了许多的parameters
        // 输出符合curve作用域的vector
        let load_points_from_file_parallelly = |reader: &mut R| -> io::Result<Vec<C>> {
            // 创建一个vector -> points_compressed
            let mut points_compressed: Vec<C::Repr> = vec![C::Repr::default(); n];
            // read_exact从reader里读数据，之后存到points_compressed里
            for points_compressed in points_compressed.iter_mut() {
                reader.read_exact((*points_compressed).as_mut())?;
            }

            let mut points = vec![C::default(); n];
            // points是一个初始化的vector
            // chunks是一个thread处理的n数量
            parallelize(&mut points, |points, chunks| {
                // iter_mut返回一个&mut的迭代器
                // enumerate返回key-value的pair
                for (i, point) in points.iter_mut().enumerate() {
                    *point = Option::from(C::from_bytes(&points_compressed[chunks + i])).unwrap();
                }
            });
            // 返回的是points
            Ok(points)
        };

        // 传入一个halo2 setup生成的file（里面都是parameters）
        // 这个函数会把file里面的随机数加载到points里，然后返回给g和g_L
        let g = load_points_from_file_parallelly(&mut reader)?;
        let g_lagrange = load_points_from_file_parallelly(&mut reader)?;
        // !到这里结束

        let mut additional_data_len = [0u8; 4];
        reader.read_exact(&mut additional_data_len[..])?;
        let additional_data_len = u32::from_le_bytes(additional_data_len);
        let mut additional_data = vec![0u8; additional_data_len as usize];

        reader.read_exact(&mut additional_data[..])?;

        Ok(Params {
            k,
            // 多了一个参数n
            n: n as u64,
            g,
            g_lagrange,
            additional_data,
        })
    }

    /// Returns verifier params with size of Lagrange bases equal to number of public inputs
    pub fn verifier<E: Engine<G1Affine = C>>(
        &self,
        public_inputs_size: usize,
    ) -> io::Result<ParamsVerifier<E>> {
        assert!(public_inputs_size < self.n as usize);
        let g_lagrange = self.g_lagrange[..public_inputs_size].to_vec();
        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();

        let additional_data = self.additional_data.clone();

        let s_g2 = E::G2Affine::read(&mut additional_data.as_slice())?;

        Ok(ParamsVerifier {
            k: self.k,
            n: self.n,
            g1: self.g[0],
            g_lagrange,
            g2,
            s_g2,
        })
    }
}

/// Wrapper type around a blinding factor.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Blind<F>(pub F);

impl<F: FieldExt> Default for Blind<F> {
    fn default() -> Self {
        Blind(F::one())
    }
}

impl<F: FieldExt> Add for Blind<F> {
    type Output = Self;

    fn add(self, rhs: Blind<F>) -> Self {
        Blind(self.0 + rhs.0)
    }
}

impl<F: FieldExt> Mul for Blind<F> {
    type Output = Self;

    fn mul(self, rhs: Blind<F>) -> Self {
        Blind(self.0 * rhs.0)
    }
}

impl<F: FieldExt> AddAssign for Blind<F> {
    fn add_assign(&mut self, rhs: Blind<F>) {
        self.0 += rhs.0;
    }
}

impl<F: FieldExt> MulAssign for Blind<F> {
    fn mul_assign(&mut self, rhs: Blind<F>) {
        self.0 *= rhs.0;
    }
}

impl<F: FieldExt> AddAssign<F> for Blind<F> {
    fn add_assign(&mut self, rhs: F) {
        self.0 += rhs;
    }
}

impl<F: FieldExt> MulAssign<F> for Blind<F> {
    fn mul_assign(&mut self, rhs: F) {
        self.0 *= rhs;
    }
}

impl<E: Engine> ParamsVerifier<E> {
    /// Returns maximum public input size allowed
    pub fn public_inputs_size(&self) -> usize {
        self.g_lagrange.len()
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<E::G1Affine> {
        MSM::new()
    }

    /// Commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain.
    pub fn commit_lagrange(&self, scalars: Vec<E::Scalar>) -> E::G1 {
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Writes params to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        let public_inputs_size = self.public_inputs_size() as u32;
        writer.write_all(&public_inputs_size.to_le_bytes())?;

        writer.write_all(self.g1.to_bytes().as_ref())?;
        writer.write_all(self.g2.to_bytes().as_ref())?;
        writer.write_all(self.s_g2.to_bytes().as_ref())?;
        for el in &self.g_lagrange {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(mut reader: R) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);

        let mut public_inputs_size = [0u8; 4];
        reader.read_exact(&mut public_inputs_size[..])?;
        let public_inputs_size = u32::from_le_bytes(public_inputs_size);

        let n = 1 << k;

        let g1 = E::G1Affine::read(&mut reader)?;
        let g2 = E::G2Affine::read(&mut reader)?;
        let s_g2 = E::G2Affine::read(&mut reader)?;
        let g_lagrange: Vec<E::G1Affine> = (0..public_inputs_size)
            .map(|_| E::G1Affine::read(&mut reader))
            .collect::<Result<_, _>>()?;

        Ok(ParamsVerifier {
            k,
            n,
            g1,
            g2,
            s_g2,
            g_lagrange,
        })
    }
}

#[cfg(test)]
use pairing::bn256::{Bn256, Fr, G1Affine};

#[test]
fn test_parameter_serialization() {
    const K: u32 = 4;

    let params0: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(K);

    let mut data: Vec<u8> = Vec::new();
    params0.write(&mut data).unwrap();
    let params1: Params<G1Affine> = Params::read(&data[..]).unwrap();

    assert_eq!(params0.k, params1.k);
    assert_eq!(params0.n, params1.n);
    assert_eq!(params0.g.len(), params1.g.len());
    assert_eq!(params0.g_lagrange.len(), params1.g_lagrange.len());

    assert_eq!(params0.g, params1.g);
    assert_eq!(params0.g_lagrange, params1.g_lagrange);
    assert_eq!(params0.additional_data, params1.additional_data);

    let public_inputs_size = 2;
    let verifier_params0: ParamsVerifier<Bn256> = params0.verifier(public_inputs_size).unwrap();

    assert_eq!(verifier_params0.k, params1.k);
    assert_eq!(verifier_params0.n, params1.n);
    assert_eq!(verifier_params0.g_lagrange.len(), public_inputs_size);
    assert_eq!(
        verifier_params0.s_g2.to_bytes().as_ref(),
        params0.additional_data
    );

    let mut data: Vec<u8> = Vec::new();
    verifier_params0.write(&mut data).unwrap();
    let verifier_params1: ParamsVerifier<Bn256> = ParamsVerifier::read(&data[..]).unwrap();
    assert_eq!(verifier_params0.k, verifier_params1.k);
    assert_eq!(verifier_params0.n, verifier_params1.n);
    assert_eq!(verifier_params0.g1, verifier_params1.g1);
    assert_eq!(verifier_params0.g2, verifier_params1.g2);
    assert_eq!(verifier_params0.s_g2, verifier_params1.s_g2);
    assert_eq!(verifier_params0.g_lagrange, verifier_params1.g_lagrange);
}

#[test]
fn test_commit_lagrange() {
    const K: u32 = 6;

    let params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(K);
    let domain = super::EvaluationDomain::new(1, K);

    let mut a = domain.empty_lagrange();

    for (i, a) in a.iter_mut().enumerate() {
        *a = Fr::from(i as u64);
    }

    let b = domain.lagrange_to_coeff(a.clone());
    assert_eq!(params.commit(&b), params.commit_lagrange(&a));
}
