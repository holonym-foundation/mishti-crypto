//! Provides simple interfaces to reconstruct ElGamal/OPRF from a threshold of responses OR from an an additive pair of responses
//! The linear homorphism of elliptic curve scalar multiplication allows both additive and threshold secret sharing
//! This enables setups that protect against collusion:
//! The result can be the sum of two results, one from a permissionless set of decentralized nodes and the other from a set of one or few nodes elected by the user
//! This additive secret sharing combined with threshold secret sharing can be used to protect against collusion, since the semi-trusted node(s) elected by the user
//! can render collusion between the decentralized nodes ineffective
use crate::{
    curve::{Curve, PointTrait},
    polynomial::lagrange_basis_at_0,
    DLEQProof, Error,
};
use itertools::izip;
/// Additive reconstruction of a point from DLEQ proofs
/// Takes lists of responses from nodes, and their corresponding public keys. Nodes and public keys should be in the same order
#[allow(dead_code)]
fn additive<const N: usize, C: Curve<N>>(
    // The point sent to nodes to be multiplied by their secrets
    point_to_multiply: C::Point,
    // The nodes' responses
    responses: Vec<DLEQProof<N, C>>,
    // The nodes' public keys
    pubkeys: Vec<C::Point>,
) -> Result<C::Point, Error> {
    let mut result = C::ZERO;
    for (proof, pk) in responses.iter().zip(pubkeys.iter()) {
        let output = proof.verify_and_get_output(pk, &point_to_multiply)?;
        result = result.add_self(&output);
    }
    Ok(result)
}
/// Threshold reconstruction of a point from DLEQ proofs
/// Takes lists of responses from nodes, their corresponding public keys, and their corresponding indices
pub fn threshold<const N: usize, C: Curve<N>>(
    // The point sent to nodes to be multiplied by their secrets
    point_to_multiply: C::Point,
    // The nodes' responses
    responses: Vec<DLEQProof<N, C>>,
    // The nodes' public keys
    pubkeys: Vec<C::Point>,
    // The nodes' indices
    indices: Vec<u32>,
) -> Result<C::Point, Error> {
    let mut result = C::ZERO;
    for (proof, pk, i) in izip!(responses, pubkeys, indices.clone()) {
        let output = proof.verify_and_get_output(&pk, &point_to_multiply)?;
        // Convert these threshold shares to additive shares by multiplying them by the corresponding lagrange basis at 0
        let at_zero = lagrange_basis_at_0::<C::FieldEl>(i, &indices);
        let as_additive_share = &output.scalar_mul(&at_zero.into());
        result = result.add_self(as_additive_share);
    }
    Ok(result)
}
/// Threshold reconstruction of a point from node indices and points they responded with. Same as `threshold` function but does not check DLEQ proofs
pub fn threshold_unchecked<const N: usize, C: Curve<N>>(responses: Vec<C::Point>, indices: Vec<u32>) -> C::Point {
    let mut result = C::ZERO;
    for (point, i) in responses.iter().zip(indices.clone()) {
        // Convert these threshold shares to additive shares by multiplying them by the corresponding lagrange basis at 0
        let at_zero = lagrange_basis_at_0::<C::FieldEl>(i, &indices);
        let as_additive_share = &point.scalar_mul(&at_zero.into());
        result = result.add_self(as_additive_share);
    }
    result
}
#[cfg(test)]
mod test {
    use super::*;
    use crate::{curve::ScalarTrait, polynomial::Polynomial, server, BabyJubJub, F256k1, Secp256k1, BABYJUBJUB};
    use ark_ed_on_bn254::EdwardsConfig;
    use ff::{Field, PrimeField};
    use k256::Scalar;
    #[test]
    fn test_additive_works() {
        let sk1 = Scalar::rand_vartime();
        let pk1 = Secp256k1::base_point_or_generator().scalar_mul(&sk1);
        let sk2 = Scalar::rand_vartime();
        let pk2 = Secp256k1::base_point_or_generator().scalar_mul(&sk2);
        let sk = sk1 + sk2;
        let pk = Secp256k1::base_point_or_generator().scalar_mul(&sk);
        assert!(pk == pk1.add_self(&pk2)); // This is asumed to be true but why not test it anyway
                                           // Give it some value to multiply the curve point:
        let r = Scalar::rand_vartime();
        let input = Secp256k1::base_point_or_generator().scalar_mul(&r);
        let res1: DLEQProof<32, Secp256k1> = server(sk1, input.encode()).unwrap();
        let res2: DLEQProof<32, Secp256k1> = server(sk2, input.encode()).unwrap();
        let result = additive(input, vec![res1, res2], vec![pk1, pk2]).unwrap();
        assert!(result == pk.scalar_mul(&r));
    }
    #[test]
    fn test_additive_fails_if_a_dleq_fails() {
        let sk1 = Scalar::rand_vartime();
        let pk1 = Secp256k1::base_point_or_generator().scalar_mul(&sk1);
        let sk2 = Scalar::rand_vartime();
        let pk2 = Secp256k1::base_point_or_generator().scalar_mul(&sk2);
        // let sk = sk1 + sk2;
        // let pk = Secp256k1::base_point_or_generator().scalar_mul(&sk);
        // Give it some value to multiply the curve point:
        let r = Scalar::rand_vartime();
        let input = Secp256k1::base_point_or_generator().scalar_mul(&r);
        let res1: DLEQProof<32, Secp256k1> = server(sk1, input.encode()).unwrap();
        let res2: DLEQProof<32, Secp256k1> = server(sk2, input.encode()).unwrap();
        let res1_: DLEQProof<32, Secp256k1> = server(sk1 + Scalar::from_u128(1), input.encode()).unwrap();
        let res2_: DLEQProof<32, Secp256k1> = server(sk2 + Scalar::from_u128(1), input.encode()).unwrap();
        assert!(additive(input, vec![res1, res2_], vec![pk1, pk2]).is_err());
        assert!(additive(input, vec![res1_, res2], vec![pk1, pk2]).is_err());
    }
    #[test]
    fn test_threshold_secp256k1() {
        // --- 2/3 threshold ---
        let secret = F256k1::from_u128(123);
        let polynomial = Polynomial::from_coeffs(vec![F256k1::from_u128(123), F256k1::from_u128(456)]);
        let secret_1 = polynomial.eval(&F256k1::from_u128(1));
        assert_eq!(secret_1, F256k1::from_u128(579));
        let secret_2 = polynomial.eval(&F256k1::from_u128(2));
        assert_eq!(secret_2, F256k1::from_u128(1035));
        let secret_3 = polynomial.eval(&F256k1::from_u128(3));
        assert_eq!(secret_3, F256k1::from_u128(1491));
        // Give it some value to multiply the curve point:
        let r = Scalar::rand_vartime();
        let input = Secp256k1::base_point_or_generator().scalar_mul(&r);
        let result_1: DLEQProof<32, Secp256k1> = server(secret_1.into(), input.encode()).unwrap();
        let result_2: DLEQProof<32, Secp256k1> = server(secret_2.into(), input.encode()).unwrap();
        let result_3: DLEQProof<32, Secp256k1> = server(secret_3.into(), input.encode()).unwrap();
        let result: DLEQProof<32, Secp256k1> = server(secret.into(), input.encode()).unwrap();
        assert_eq!(
            result.output_point,
            threshold(
                input,
                vec![result_1.clone(), result_2.clone()],
                vec![
                    Secp256k1::base_point_or_generator().scalar_mul(&secret_1.into()),
                    Secp256k1::base_point_or_generator().scalar_mul(&secret_2.into())
                ],
                vec![1, 2]
            )
            .unwrap()
        );
        assert_eq!(
            result.output_point,
            threshold(
                input,
                vec![result_3, result_1],
                vec![
                    Secp256k1::base_point_or_generator().scalar_mul(&secret_3.into()),
                    Secp256k1::base_point_or_generator().scalar_mul(&secret_1.into())
                ],
                vec![3, 1]
            )
            .unwrap()
        );
        // --- For 1/2 threshold ---
        let secret = F256k1::from_u128(123);
        let polynomial = Polynomial::from_coeffs(vec![F256k1::from_u128(123)]);
        let secret_1 = polynomial.eval(&F256k1::from_u128(1));
        assert_eq!(secret_1, F256k1::from_u128(123));
        let secret_2 = polynomial.eval(&F256k1::from_u128(1));
        assert_eq!(secret_2, F256k1::from_u128(123));
        // Give it some value to multiply the curve point:
        let r = Scalar::rand_vartime();
        let input = Secp256k1::base_point_or_generator().scalar_mul(&r);
        let result_1: DLEQProof<32, Secp256k1> = server(secret_1.into(), input.encode()).unwrap();
        let result_2: DLEQProof<32, Secp256k1> = server(secret_2.into(), input.encode()).unwrap();
        let result: DLEQProof<32, Secp256k1> = server(secret.into(), input.encode()).unwrap();
        assert_eq!(
            result.output_point,
            threshold(input, vec![result_1], vec![Secp256k1::base_point_or_generator().scalar_mul(&secret_1.into())], vec![1]).unwrap()
        );
        assert_eq!(
            result.output_point,
            threshold(input, vec![result_2], vec![Secp256k1::base_point_or_generator().scalar_mul(&secret_2.into())], vec![2]).unwrap()
        );
    }
    #[test]
    fn test_threshold_babyjub() {
        // --- 2/3 threshold ---
        let secret = BABYJUBJUB::from_u128(123);
        let polynomial = Polynomial::from_coeffs(vec![BABYJUBJUB::from_u128(123), BABYJUBJUB::from_u128(456)]);
        let secret_1 = polynomial.eval(&BABYJUBJUB::from_u128(1));
        assert_eq!(secret_1, BABYJUBJUB::from_u128(579));
        let secret_2 = polynomial.eval(&BABYJUBJUB::from_u128(2));
        assert_eq!(secret_2, BABYJUBJUB::from_u128(1035));
        let secret_3 = polynomial.eval(&BABYJUBJUB::from_u128(3));
        assert_eq!(secret_3, BABYJUBJUB::from_u128(1491));
        // Give it some value to multiply the curve point:
        let r = <BabyJubJub as Curve<32>>::Scalar::rand_vartime();
        let input = BabyJubJub::base_point_or_generator().scalar_mul(&r);
        let result_1: DLEQProof<32, BabyJubJub> = server(secret_1.into(), input.encode()).unwrap();
        let result_2: DLEQProof<32, BabyJubJub> = server(secret_2.into(), input.encode()).unwrap();
        let result_3: DLEQProof<32, BabyJubJub> = server(secret_3.into(), input.encode()).unwrap();
        let result: DLEQProof<32, BabyJubJub> = server(secret.into(), input.encode()).unwrap();
        assert_eq!(
            result.output_point,
            threshold(
                input,
                vec![result_1.clone(), result_2.clone()],
                vec![
                    BabyJubJub::base_point_or_generator().scalar_mul(&secret_1.into()),
                    BabyJubJub::base_point_or_generator().scalar_mul(&secret_2.into())
                ],
                vec![1, 2]
            )
            .unwrap()
        );
        assert_eq!(
            result.output_point,
            threshold(
                input,
                vec![result_3, result_1],
                vec![
                    BabyJubJub::base_point_or_generator().scalar_mul(&secret_3.into()),
                    BabyJubJub::base_point_or_generator().scalar_mul(&secret_1.into())
                ],
                vec![3, 1]
            )
            .unwrap()
        );
        // --- For 1/2 threshold ---
        let secret = BABYJUBJUB::from_u128(123);
        let polynomial = Polynomial::from_coeffs(vec![BABYJUBJUB::from_u128(123)]);
        let secret_1 = polynomial.eval(&BABYJUBJUB::from_u128(1));
        assert_eq!(secret_1, BABYJUBJUB::from_u128(123));
        let secret_2 = polynomial.eval(&BABYJUBJUB::from_u128(1));
        assert_eq!(secret_2, BABYJUBJUB::from_u128(123));
        // Give it some value to multiply the curve point:
        let r = <BabyJubJub as Curve<32>>::Scalar::rand_vartime();
        let input = BabyJubJub::base_point_or_generator().scalar_mul(&r);
        let result_1: DLEQProof<32, BabyJubJub> = server(secret_1.into(), input.encode()).unwrap();
        let result_2: DLEQProof<32, BabyJubJub> = server(secret_2.into(), input.encode()).unwrap();
        let result: DLEQProof<32, BabyJubJub> = server(secret.into(), input.encode()).unwrap();
        assert_eq!(
            result.output_point,
            threshold(input, vec![result_1], vec![BabyJubJub::base_point_or_generator().scalar_mul(&secret_1.into())], vec![1]).unwrap()
        );
        assert_eq!(
            result.output_point,
            threshold(input, vec![result_2], vec![BabyJubJub::base_point_or_generator().scalar_mul(&secret_2.into())], vec![2]).unwrap()
        );
    }
    #[test]
    fn test_threshold_fails_if_a_dleq_fails() {
        // --- 2/3 threshold ---
        // let mut secret = F256k1::from_u128(123);
        let polynomial = Polynomial::from_coeffs(vec![F256k1::from_u128(123), F256k1::from_u128(456)]);
        let secret_1 = polynomial.eval(&F256k1::from_u128(1));
        assert_eq!(secret_1, F256k1::from_u128(579));
        let secret_2 = polynomial.eval(&F256k1::from_u128(2));
        assert_eq!(secret_2, F256k1::from_u128(1035));
        let secret_3 = polynomial.eval(&F256k1::from_u128(3));
        assert_eq!(secret_3, F256k1::from_u128(1491));
        // Give it some value to multiply the curve point:
        let r = Scalar::rand_vartime();
        let input = Secp256k1::base_point_or_generator().scalar_mul(&r);
        let result_1: DLEQProof<32, Secp256k1> = server(secret_1.into(), input.encode()).unwrap();
        let result_2: DLEQProof<32, Secp256k1> = server(secret_2.into(), input.encode()).unwrap();
        // let result_3: DLEQProof<32, Secp256k1> = server(secret_3.into(), input.encode()).unwrap();
        // let result: DLEQProof<32, Secp256k1> = server(secret.into(), input.encode()).unwrap();
        assert!(threshold(
            input,
            vec![result_1.clone(), result_2.clone()],
            vec![
                Secp256k1::base_point_or_generator().scalar_mul(&secret_3.into()),
                Secp256k1::base_point_or_generator().scalar_mul(&secret_2.into())
            ],
            vec![1, 2]
        )
        .is_err());
    }
}
