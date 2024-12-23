//! Copiedfrom github.com/holonym-foundation/babyjubjub-elgamal-project polynomial.rs
//! with added generics
use crate::curve::{Curve, PointTrait};
use blake2::{Blake2b512, Digest};
use ff::PrimeField;
use rand::{rngs::StdRng, thread_rng};
use rand_core::SeedableRng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
// impl Serialize for Polynomial {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//         where
//             S: serde::Serializer {
//                 let mut seq = serializer.serialize_seq(Some(self.coefficients.len()))?;
//                 self.coefficients.iter().for_each(
//                     |coef|  { seq.serialize_element(&coef.to_string()); }
//                 );
//                 seq.end()
//             }
// }
#[derive(Serialize, Deserialize)]
pub struct Polynomial<F: PrimeField> {
    coefficients: Vec<F>,
}
impl<F: PrimeField> Polynomial<F> {
    /// Coefficents are in ascending order, i.e. the value and index zero represents coefficient for x^0
    pub fn from_coeffs(coeffs: Vec<F>) -> Polynomial<F> { Polynomial { coefficients: coeffs } }
    // Creates a random polynomial with elements in F
    pub fn random_polynomial(degree: usize) -> Polynomial<F> {
        let coeffs = (0..degree + 1).map(|_| F::random(&mut thread_rng())).collect::<Vec<F>>();
        Polynomial { coefficients: coeffs }
    }
    // Creates a random polynomial with a secret value set as free term (used for SSS)
    pub fn random_polynomials_with_secret(degree: usize, secret: F) -> Polynomial<F> {
        let mut coeffs = (0..degree + 1).map(|_| F::random(&mut thread_rng())).collect::<Vec<F>>();
        coeffs[0] = secret;
        Polynomial { coefficients: coeffs }
    }
    /// Genereates polynomial from a random seed by repeatedly hashing it to get eeach new coefficient
    pub fn from_seed(seed: &[u8; 32], degree: usize) -> Polynomial<F> {
        assert!(seed.len() == 32, "seed must be 32 bytes");
        let mut coeffs: Vec<F> = vec![];
        let mut recent: [u8; 32] = *seed;
        for _ in 0..degree + 1 {
            let mut h = Blake2b512::new();
            h.update(recent);
            recent = (*h.finalize().as_slice()).try_into().unwrap();
            let seed: <StdRng as SeedableRng>::Seed = recent;
            let prg = StdRng::from_seed(seed);
            coeffs.push(F::random(prg));
        }
        Polynomial::from_coeffs(coeffs)
    }
    /// Unsafe for exponents polynomials larger than the max possible u64. But usize should never exceed u64 and i doubt anyone can use this
    /// with over 2^64 nodes!
    pub fn eval(&self, x: &F) -> F { self.coefficients.iter().enumerate().map(|(i, coeff)| x.pow([i as u64]).mul(coeff)).sum::<F>() }
    /// Degree of the polynomial
    pub fn deg(&self) -> usize { self.coefficients.len() - 1 }
    /// adds to another polynomial of same degree
    pub fn add_same_deg(&self, other_polynomial: &Polynomial<F>) -> Polynomial<F> {
        assert_eq!(
            self.deg(),
            other_polynomial.deg(),
            "Error adding polynomials with coefficients {:?} and {:?} Currently, adding polynomials is only supported for polynomials of the same degree",
            self.coefficients,
            other_polynomial.coefficients
        );
        let new_coefs = self.coefficients.iter().zip(other_polynomial.coefficients.clone()).map(|(a, b)| b + a).collect();
        Polynomial { coefficients: new_coefs }
    }
}
// Returns L_i(0) where L_i(x) is the unique polynomical such that L_i(i) = 1 and L_i(x) = 0 for all x in set indices other than i
pub fn lagrange_basis_at_0<F: PrimeField>(i: u32, indices: &[u32]) -> F {
    assert!(i > 0, "i must be greater than 0");
    // assert!(n > 0, "n must be greater than 0");
    let one = F::ONE;
    let mut acc = one;
    let i_ = F::from_str_vartime(&i.to_string()).unwrap();
    // since we are evaluating L_i(x) where x=0, can set x to 0 in formula for lagrange basis. Formula becomes becomes product of j / (j-i) for all j not equal to i
    // while j <= n {
    for j in indices.iter() {
        if *j != i {
            let j_ = F::from_u128(*j as u128);
            // numerator = j, demoninator = j - i
            let mut denominator = j_;
            denominator.sub_assign(&i_);
            acc.mul_assign(&j_);
            acc.mul_assign(&denominator.invert().unwrap());
        }
    }
    acc
}
// Returns evaluation of the polynomial at indexes along with the commitment of the polynomial. Used for Feldman VSS
pub fn feldman_vss<const N: usize, C: Curve<N>, T: Clone>(poly: Polynomial<C::FieldEl>, set: &HashMap<u128, T>, t: usize) -> (HashMap<u128, C::FieldEl>, Vec<C::Point>) {
    let mut y = HashMap::new();
    let mut v = Vec::new();
    // Evaluation of the polynomial for each index value included in the network
    let set = set.clone();
    for (key, _value) in set.into_iter() {
        y.entry(key).or_insert(poly.eval(&C::FieldEl::from_u128(key)));
    }
    // Commitment of each of the polynomial coefficients
    for j in 0..t {
        let coeff = poly.coefficients[j].into();
        let com = C::base_point_or_generator().scalar_mul(&coeff);
        v.push(com);
    }
    (y, v)
}
pub fn verify_vss<const N: usize, C: Curve<N>>(index: u128, share: C::FieldEl, checks: &[C::Point]) -> bool {
    let res = C::base_point_or_generator().scalar_mul(&share.into());
    let mut cop = checks.to_vec();
    let mut accum: C::Point = cop[0].clone();
    let mut exp = 1;
    cop.remove(0);
    for i in cop {
        exp *= index;
        let temp = C::FieldEl::from_u128(exp);
        let res2 = i.scalar_mul(&temp.into());
        accum = accum.add_self(&res2);
    }
    res.eq(&accum)
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::F256k1;
    use std::ops::{AddAssign, MulAssign};
    #[test]
    fn test_polynomial() {
        // polynomial is 123456789 + 69x + 987654321x^2
        let coeffs: Vec<F256k1> = [123456789u128, 69, 987654321].map(|x| F256k1::from_u128(x)).to_vec();
        let polynomial = Polynomial::from_coeffs(coeffs);
        assert!(polynomial.eval(&F256k1::from_u128(0)) == F256k1::from_u128(123456789));
        assert!(polynomial.eval(&F256k1::from_u128(123)) == F256k1::from_u128(14942345687685));
    }
    #[test]
    fn test_random_polynomial_degree() {
        let p0 = Polynomial::<F256k1>::random_polynomial(0);
        let p1 = Polynomial::<F256k1>::random_polynomial(1);
        let p2 = Polynomial::<F256k1>::random_polynomial(2);
        let p3 = Polynomial::<F256k1>::random_polynomial(3);
        assert!(p0.coefficients.len() == 1);
        assert!(p1.coefficients.len() == 2);
        assert!(p2.coefficients.len() == 3);
        assert!(p3.coefficients.len() == 4);
    }
    #[test]
    fn test_lagrange_basis_at_0_2of2() {
        // TODO: refactor this to be more concise
        // test for reconstructing y-intercept of line with points (1,5) and (2,6). test that y-intercept is 4
        // let n: u32 = 2; // n  =  number of shares  =  degree of polynomial + 1
        let l1 = lagrange_basis_at_0::<F256k1>(1 as u32, &vec![1, 2]);
        let l2 = lagrange_basis_at_0::<F256k1>(2 as u32, &vec![1, 2]);
        let y1 = F256k1::from_str_vartime("5").unwrap();
        let y2 = F256k1::from_str_vartime("6").unwrap();
        // calculate l1y1+l2y2
        // part 1
        let mut result = l1.clone();
        result.mul_assign(&y1);
        // part 2
        let mut part2 = l2.clone();
        part2.mul_assign(&y2);
        result.add_assign(&part2);
        assert!(result.eq(&F256k1::from_str_vartime("4").unwrap()));
    }
    // Now, try the same thing but for a degree-2 polynomial: 3x^2+100x+123. Points are (1, 226), (2, 335) and (3, 450)
    // Test that y-intercept is 123
    #[test]
    fn test_lagrange_basis_at_0_3of3() {
        let nodes_to_decrypt_from: Vec<u32> = vec![1, 2, 3];
        // Now, try the same thing but for a degree-2 polynomial (3/3 secret shared)
        let l1 = lagrange_basis_at_0::<F256k1>(1 as u32, &nodes_to_decrypt_from);
        let l2 = lagrange_basis_at_0::<F256k1>(2 as u32, &nodes_to_decrypt_from);
        let l3 = lagrange_basis_at_0::<F256k1>(3 as u32, &nodes_to_decrypt_from);
        let y1 = F256k1::from_str_vartime("226").unwrap();
        let y2 = F256k1::from_str_vartime("335").unwrap();
        let y3 = F256k1::from_str_vartime("450").unwrap();
        // calculate l1y1+l2y2+l3y3
        // part 1
        let mut result = l1.clone();
        result.mul_assign(&y1);
        // part 2
        let mut part2 = l2.clone();
        part2.mul_assign(&y2);
        // part 3
        let mut part3 = l3.clone();
        part3.mul_assign(&y3);
        result.add_assign(&part2);
        result.add_assign(&part3);
        assert!(result.eq(&F256k1::from_str_vartime("123").unwrap()));
    }
    // Now, try the same thing but for a degree-1 polynomial: 123x+321. Points are (1, 444), (2, 567) and (3, 690)
    // Test that y-intercept is 321 and can be reconstructed from nodes 1 and 2, nodes 2 and 3, and nodes 1 and 3
    #[test]
    fn test_lagrange_basis_at_0_2of3_successful_reconsrtruction_for_each_pair_of_2_nodes() {
        // Each of these pairs should be sufficient to reconstruct the shared secret
        // Pairs consist of node indices and their corresponding lagrange bases at 0
        let pairs: Vec<[(u32, F256k1); 2]> = vec![
            [(1, lagrange_basis_at_0::<F256k1>(1 as u32, &vec![1, 2])), (2, lagrange_basis_at_0::<F256k1>(2 as u32, &vec![1, 2]))],
            [(2, lagrange_basis_at_0::<F256k1>(2 as u32, &vec![2, 3])), (3, lagrange_basis_at_0::<F256k1>(3 as u32, &vec![2, 3]))],
            [(1, lagrange_basis_at_0::<F256k1>(1 as u32, &vec![1, 3])), (3, lagrange_basis_at_0::<F256k1>(3 as u32, &vec![1, 3]))],
        ];
        let y1 = F256k1::from_str_vartime("444").unwrap();
        let y2 = F256k1::from_str_vartime("567").unwrap();
        let y3 = F256k1::from_str_vartime("690").unwrap();
        let secret_share = |x| {
            if x == 1 {
                y1
            } else if x == 2 {
                y2
            } else if x == 3 {
                y3
            } else {
                panic!("Invalid node index")
            }
        };
        pairs.iter().for_each(|pair| {
            let (idx0, lb0) = pair[0];
            let (idx1, lb1) = pair[1];
            // Add up the secret shares * lagrange bases at 0 for each pair. This should recosntruct the secret, which should be the same for each pair
            let mut result = lb0.clone();
            result.mul_assign(&secret_share(idx0));
            let mut part2 = lb1.clone();
            part2.mul_assign(&secret_share(idx1));
            result.add_assign(&part2);
            assert!(result.eq(&F256k1::from_str_vartime("321").unwrap()));
        });
    }
    #[test]
    pub fn test_add_same_deg() {
        let p1 = Polynomial::from_coeffs(vec![F256k1::from_u128(100), F256k1::from_u128(69), F256k1::from_u128(0), F256k1::from_u128(7)]);
        let p2 = Polynomial::from_coeffs(vec![F256k1::from_u128(9), F256k1::from_u128(1), F256k1::from_u128(5), F256k1::from_u128(0)]);
        let p3 = p1.add_same_deg(&p2);
        assert!(
            (p3.coefficients[0] == F256k1::from_u128(109))
                && (p3.coefficients[1] == F256k1::from_u128(70))
                && (p3.coefficients[2] == F256k1::from_u128(5))
                && (p3.coefficients[3] == F256k1::from_u128(7))
        )
    }
}
