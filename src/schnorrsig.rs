use crate::{hash512, serialization, BabyJubJub, Curve, Error, PointTrait, ScalarTrait};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
pub trait SchnorrSignable<const N: usize, C: Curve<N>> {
    /// Returns (R, s)
    fn sign(&self, msg: &[u8]) -> SchnorrSig<N, C>;
    fn verify(msg: &[u8], pubkey: &C::Point, sig: &SchnorrSig<N, C>) -> Result<(), Error>;
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SchnorrSig<const N: usize, C: Curve<N>> {
    #[serde(with = "serialization::point_hex")]
    R: C::Point,
    #[serde(with = "serialization::scalar_hex")]
    s: C::Scalar,
}
impl<const N: usize, C: Curve<N>> SchnorrSignable<N, C> for C::Scalar {
    fn sign(&self, msg: &[u8]) -> SchnorrSig<N, C> {
        let modulus = BigUint::from_bytes_be(&C::FIELD_MODULUS_BE);
        let nonce = Self::rand_vartime();
        let pubnonce = C::base_point_or_generator().scalar_mul(&nonce);
        let pubkey = C::base_point_or_generator().scalar_mul(self);
        let mut preimg = Vec::new();
        preimg.extend_from_slice(&pubnonce.encode());
        preimg.extend_from_slice(&pubkey.encode());
        preimg.extend_from_slice(msg);
        let h = BigUint::from_bytes_be(&hash512(&preimg)) % modulus;
        let s = nonce + self.clone() * Self::from_biguint_vartime(h).unwrap();
        // R, s
        SchnorrSig { R: pubnonce, s }
    }
    fn verify(msg: &[u8], pubkey: &C::Point, sig: &SchnorrSig<N, C>) -> Result<(), Error> {
        let modulus = BigUint::from_bytes_be(&C::FIELD_MODULUS_BE);
        let (pubnonce, s) = (sig.R.clone(), sig.s.clone());
        let mut preimg = Vec::new();
        preimg.extend_from_slice(&pubnonce.encode());
        preimg.extend_from_slice(&pubkey.encode());
        preimg.extend_from_slice(msg);
        let h = BigUint::from_bytes_be(&hash512(&preimg)) % modulus;
        let lhs = C::base_point_or_generator().scalar_mul(&s);
        let rhs = pubkey.scalar_mul(&Self::from_biguint_vartime(h).unwrap()).add_self(&pubnonce);
        if lhs == rhs {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}
/// Useful for babyjubjub encryption where the user signs with an ephemeral private key and then feed that private key into the ElGamal encryption circuit
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EphemeralPrivateKeyWithSig {
    #[serde(with = "serialization::scalar_hex")]
    pub private_key: <BabyJubJub as Curve<32>>::Scalar,
    pub signature: SchnorrSig<32, BabyJubJub>,
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BabyJubJub, Curve, Secp256k1};
    use ark_ed_on_bn254::Fr;
    use ethers::types::Address;
    use k256::Scalar;
    #[test]
    fn test_schnorrsig_secp() {
        let sk = Scalar::rand_vartime();
        let pk = Secp256k1::base_point_or_generator().scalar_mul(&sk);
        let msg = b"hello world";
        let sig: SchnorrSig<32, Secp256k1> = sk.sign(msg);
        assert!(Scalar::verify(msg, &pk, &sig).is_ok());
    }
    #[test]
    fn test_schnorrsig_secp_invalid() {
        let sk = Scalar::rand_vartime();
        let pk = Secp256k1::base_point_or_generator().scalar_mul(&sk);
        let msg = b"hello world";
        let sig: SchnorrSig<32, Secp256k1> = sk.sign(msg);
        let mut msg2 = msg.to_vec();
        msg2[0] = b'H';
        assert!(Scalar::verify(&msg2, &pk, &sig).is_err());
    }
    #[test]
    fn test_schnorrsig_babyjub() {
        let sk = Fr::rand_vartime();
        let pk = BabyJubJub::base_point_or_generator().scalar_mul(&sk);
        let msg = b"hello world";
        let sig: SchnorrSig<32, BabyJubJub> = sk.sign(msg);
        // let sig = <Scalar as SchnorrSig<32, BabyJubJub<32>>::sign(&sk, msg);
        assert!(Fr::verify(msg, &pk, &sig).is_ok());
    }
    // Used for creating an integration test with the browser
    #[test]
    fn generate_some_test_values() {
        let secret = <BabyJubJub as Curve<32>>::Scalar::rand_vartime();
        let signed: SchnorrSig<32, BabyJubJub> = secret.sign("0x248002ce5220b12d87bdbe148e04ee4bf29682f4".parse::<Address>().expect("invalid conditions contract address").as_bytes());
        let result = serde_json::to_string_pretty(&EphemeralPrivateKeyWithSig {
            private_key: secret,
            signature: signed,
        })
        .unwrap();
        println!("{}", result);
    }
}
