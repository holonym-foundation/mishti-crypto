#![allow(non_snake_case)]
#![feature(generic_const_exprs)]
// #![feature(effects)]
#![feature(const_trait_impl)]
#![feature(concat_idents)]
use bcrypt::DEFAULT_COST;
#[allow(unused_imports)]
use blake2::{Blake2b512, Digest as Digest_blake2};
pub use curve::{BabyJubJub, Curve, PointTrait, ScalarTrait, Secp256k1, BABYJUBJUB};
use ff::*;
#[allow(unused_imports)]
use k256::{
    elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint},
    AffinePoint, EncodedPoint, Scalar,
};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use sha3::Sha3_256;
use std::fmt::{self, Formatter};
extern crate ff;
pub mod curve;
pub mod dkg;
pub mod encryption;
pub mod node_selection;
pub mod polynomial;
pub mod reconstruct;
pub mod resharing;
pub mod schnorrsig;
pub mod serialization;
pub mod twisted_conversion;
pub mod zkinjmask;
// Create a new primefield for the group defined by the base point. This is the subgroup when the curve has a cofactor.
// This is what's used for threshold cryptography within the curve
#[derive(PrimeField)]
#[PrimeFieldModulus = "115792089237316195423570985008687907852837564279074904382605163141518161494337"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "big"]
pub struct F256k1([u64; 5]);
#[derive(Debug)]
pub enum Error {
    InvalidInput,
    InvalidSignature,
    ExtremelyRareErrorInputUnhashableToCurve,
    InvalidDLEQProof,
    UnknownError,
    Other(String),
}
impl std::error::Error for Error {}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidInput => write!(f, "Invalid input"),
            Error::ExtremelyRareErrorInputUnhashableToCurve => {
                write!(f, "Extremely rare error: input unhashable to curve")
            }
            Error::InvalidDLEQProof => write!(f, "Invalid DLEQ proof"),
            Error::InvalidSignature => write!(f, "Invalid signature"),
            Error::UnknownError => write!(f, "Unknown error"),
            Error::Other(data) => write!(f, "Error :{:?}", data),
        }
    }
}
fn hash512<T: AsRef<[u8]>>(preimage: T) -> [u8; 64] {
    let mut hasher = Blake2b512::new();
    hasher.update(preimage);
    hasher.finalize().as_slice().try_into().unwrap() //should never panic
}
fn hash256<T: AsRef<[u8]>>(preimage: T) -> [u8; 32] {
    let mut hasher = Sha3_256::new();
    hasher.update(preimage);
    hasher.finalize().as_slice().try_into().unwrap() //should never panic
}
/// Local KDF based on username (or identifier / salt preimage) and password (or secret) before bcrypt. Bcrypt was chosen instead of argon2 it is said to be more secure for times under 1000ms
pub fn local_kdf<T: AsRef<[u8]>>(username: T, password: T) -> Result<String, Error> {
    // salt is just for bcrypt so can be hash of username -- i don't see a need to make it unguessable but rather just unique per user.
    let salt_: [u8; 32] = hash256(&username);
    let salt: [u8; 16] = salt_[0..16].try_into().unwrap(); // OK to unwrap, never should fail
    let derived = bcrypt::hash_with_salt(password, DEFAULT_COST, &salt).map_err(|_| Error::InvalidInput)?;
    Ok(derived.to_string())
}
/// Generates an `EncodedPoint` representing the client's first message to the server given their `raw_msg`, and the client's secret mask to store until `oprf_client_2` needs it
pub fn oprf_client_1<const N: usize, C: Curve<N>, T: AsRef<[u8]>>(username: T, password: T) -> Result<(Vec<u8>, C::Scalar), Error> {
    let local_kdf_result = local_kdf(username, password)?;
    let secret_mask = C::Scalar::rand_vartime();
    let hashed2curve: <C as Curve<N>>::Point = C::hash_to_curve(&local_kdf_result.into_bytes())?;
    let masked = hashed2curve.scalar_mul(&secret_mask);
    // Apply point compression for security (since the server will now see only the x-coordinate, it does not need to check for an invalid curve attack)
    Ok((masked.encode().to_vec(), secret_mask))
}
/// Unmasks the server's response to the client's first message, returning the Diffie Hellman result. Before doing so, it verifies a proof that the server applied the same secret x to arrive at the result as it did to arrive at it's public key
pub fn oprf_client_2<const N: usize, C: Curve<N>>(my_masked_point: &C::Point, my_mask: &C::Scalar, server_pubkey: &C::Point, server_response: &DLEQProof<N, C>) -> Result<String, Error> {
    let server_output = server_response.verify_and_get_output(server_pubkey, my_masked_point)?;
    let inverted = my_mask.mul_inv();
    if inverted.is_some().unwrap_u8() == 0 {
        return Err(Error::InvalidInput);
    }
    Ok(C::hash_from_curve(server_output.scalar_mul(&inverted.unwrap())).to_str_radix(16))
}
/// Diffie Hellman on the masked client value and the server secret
pub fn server<const N: usize, C: Curve<N>>(server_secret: C::Scalar, oprf_client_masked: Vec<u8>) -> Result<DLEQProof<N, C>, Error> {
    let as_pt = C::Point::from_encoded(&oprf_client_masked)?;
    // This does the multiplication and proves it
    DLEQProof::new(as_pt, server_secret)
}
/// Proof that you know scalar x for public values xA and xB. This uses a private nonce r and a challenge generated by the Fiat-Shamir heuristic
// #[serde(into = "DLEQProofSerializable")]
// #[serde(try_from = "DLEQProofSerializable")]
#[derive(Serialize, Deserialize, Clone)]
pub struct DLEQProof<const N: usize, C: Curve<N>> {
    /// Input that should be multiplied by the secret scalar
    #[serde(with = "serialization::point_hex")]
    pub input_point: C::Point,
    /// Secret scalar times generator
    #[serde(with = "serialization::point_hex")]
    pub pubkey: C::Point,
    /// Secret scalar times input_point
    #[serde(with = "serialization::point_hex")]
    pub output_point: C::Point,
    /// nonce times the generator
    #[serde(with = "serialization::point_hex")]
    pub r_pub: C::Point,
    /// nonce times the input_point
    #[serde(with = "serialization::point_hex")]
    pub r_in: C::Point,
    /// Challenge generated by the Fiat-Shamir heuristic
    #[serde(with = "serialization::scalar_hex")]
    pub challenge: C::Scalar,
    /// Response to the challenge
    #[serde(with = "serialization::scalar_hex")]
    pub response: C::Scalar,
}
impl<const N: usize, C: Curve<N>> fmt::Debug for DLEQProof<N, C>
where
    C: Curve<N>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.debug_struct("DLEQProof").finish() }
}
impl<const N: usize, C: Curve<N>> DLEQProof<N, C> {
    fn challenge_hash(input_point: &C::Point, pubkey: &C::Point, output_point: &C::Point, r_pub: &C::Point, r_in: &C::Point) -> Result<C::Scalar, Error> {
        // concatenate all points and hash
        let mut concatted: Vec<u8> = Vec::new();
        [&C::base_point_or_generator(), input_point, pubkey, output_point, r_pub, r_in].iter().for_each(|pt| {
            let encoded = pt.encode();
            concatted.extend(encoded);
        });
        // hash to 2x modulus size to ensure negligable nonuniformity after reducing mod n
        let digest = hash512(&concatted);
        let digest_modn = BigUint::from_bytes_be(&digest) % BigUint::from_bytes_be(&C::FIELD_MODULUS_BE);
        C::Scalar::from_biguint_vartime(digest_modn)
    }
    /// Creates a Schnorr DLEQ proof using of multiplying input_point by secret_key
    pub fn new(input_point: C::Point, secret_key: C::Scalar) -> Result<Self, Error> {
        let r = C::Scalar::rand_vartime();
        let pubkey = C::base_point_or_generator().scalar_mul(&secret_key);
        let output_point = input_point.scalar_mul(&secret_key);
        let r_pub = C::base_point_or_generator().scalar_mul(&r);
        let r_in = input_point.scalar_mul(&r);
        let challenge = Self::challenge_hash(&input_point, &pubkey, &output_point, &r_pub, &r_in)?;
        let response = r - challenge.clone() * secret_key;
        Ok(Self {
            input_point,
            pubkey,
            output_point,
            r_pub,
            r_in,
            challenge,
            response,
        })
    }
    /// Verifies a DLEQ proof. Inputs are the the prover's public key and the point which should be multiplied the prover's secret key.
    /// Returns the result of the secret key multiplied by the original point if and only if the proof is valid. If the proof is not valid,
    /// returns an error.
    pub fn verify_and_get_output(&self, pubkey: &C::Point, point_to_multiply: &C::Point) -> Result<C::Point, Error> {
        let should_be_rA = C::base_point_or_generator().scalar_mul(&self.response).add_self(&self.pubkey.scalar_mul(&self.challenge));
        let should_be_rB = self.input_point.scalar_mul(&self.response).add_self(&self.output_point.scalar_mul(&self.challenge));
        let should_be_challenge = Self::challenge_hash(point_to_multiply, &self.pubkey, &self.output_point, &should_be_rA, &should_be_rB)?;
        if (should_be_challenge == self.challenge) && (self.input_point == *point_to_multiply) && (self.pubkey == *pubkey) {
            Ok(self.output_point.clone())
        } else {
            Err(Error::InvalidDLEQProof)
        }
    }
}
// #[derive(Serialize, Deserialize)]
// pub struct WasmClientStep1Response {
//     pub masked: Vec<u8>,
//     pub secret_mask: Scalar,
// }
// #[wasm_bindgen]
// pub fn oprf_client_step1(username: &str, password: &str) -> Result<JsValue, JsError> {
//     let (masked, secret_mask) =
//         oprf_client_1::<32, Secp256k1, &[u8]>(username.as_bytes(), password.as_bytes())?;
//     Ok(serde_wasm_bindgen::to_value(&WasmClientStep1Response {
//         masked,
//         secret_mask,
//     })?)
// }
// #[wasm_bindgen]
// pub fn oprf_client_step2(
//     my_masked_point: JsValue,
//     my_mask: JsValue,
//     server_pubkey: JsValue,
//     server_response: JsValue,
// ) -> Result<String, JsError> {
//     let masked: AffinePoint = serde_wasm_bindgen::from_value(my_masked_point)?;
//     let mask: Scalar = serde_wasm_bindgen::from_value(my_mask)?;
//     let resp: DLEQProof<32, Secp256k1> = serde_wasm_bindgen::from_value(server_response)?;
//     let pubkey: AffinePoint = serde_wasm_bindgen::from_value(server_pubkey)?;
//     Ok(oprf_client_2(&masked, &mask, &pubkey, &resp)?)
// }
// #[wasm_bindgen]
// pub fn enable_detailed_wasm_errors() {
//     console_error_panic_hook::set_once();
// }
// TEST that mask(unmask(msg)) == msg
#[cfg(test)]
mod test {
    use super::*;
    use rand_core::OsRng;
    #[test]
    fn secret_key_serialization() {
        let secret_key: Scalar = Scalar::generate_vartime(&mut OsRng);
        let serialized = serde_json::to_string(&secret_key).unwrap();
        let deserialized: Scalar = serde_json::from_str(&serialized).unwrap();
        assert_eq!(secret_key, deserialized);
    }
    #[test]
    // will panic if it doesn't work
    fn oprf_works() {
        let server_secret = Scalar::generate_vartime(&mut OsRng);
        let server_pubkey = AffinePoint::GENERATOR * &server_secret;
        let username = "myemail@gmail.io".as_bytes();
        let password = "password123".as_bytes();
        let (oprf_client_masked, secret_mask) = oprf_client_1::<32, Secp256k1, &[u8]>(username, password).unwrap();
        let server_response: DLEQProof<32, Secp256k1> = server(server_secret, oprf_client_masked.clone()).unwrap();
        let _result = oprf_client_2(
            &AffinePoint::from_encoded(&oprf_client_masked.clone()).unwrap(),
            &secret_mask,
            &server_pubkey.to_affine(),
            &server_response,
        )
        .unwrap();
    }
    #[test]
    // Ensures that running OPRF gives hash2scalar(server_secret * hash2curve(bcrypt(msg))). This essentially checks that the masking and unmasking was done correctly
    fn oprf_outputs_correct_value() {
        let server_secret = Scalar::generate_vartime(&mut OsRng);
        let server_pubkey = AffinePoint::GENERATOR * &server_secret;
        let username = "email@e.mail".as_bytes();
        let password = "hunter2".as_bytes();
        let (oprf_client_masked, secret_mask) = oprf_client_1::<32, Secp256k1, &[u8]>(username, password).unwrap();
        let server_response: DLEQProof<32, Secp256k1> = server(server_secret, oprf_client_masked.clone()).unwrap();
        let result = oprf_client_2(&AffinePoint::from_encoded(&oprf_client_masked).unwrap(), &secret_mask, &server_pubkey.to_affine(), &server_response).unwrap();
        let localkdf = local_kdf(username, password).unwrap();
        let hashed2curve = Secp256k1::hash_to_curve(&localkdf.as_bytes().to_vec()).unwrap();
        let multiplied = (hashed2curve * server_secret).to_encoded_point(true);
        let expected = hash512(&multiplied.as_bytes());
        let expected_modn = BigUint::from_bytes_be(&expected) % BigUint::from_bytes_be(&Secp256k1::FIELD_MODULUS_BE);
        println!("hex was {}", expected_modn.to_str_radix(16));
        assert_eq!(expected_modn.to_str_radix(16), result);
    }
    #[test]
    fn bad_pubkey_fails_oprf() {
        let server_secret = Scalar::generate_vartime(&mut OsRng);
        let server_wrong_pubkey = AffinePoint::GENERATOR * Scalar::generate_vartime(&mut OsRng);
        let username = "email@ema.il".as_bytes();
        let password = "Hunter2".as_bytes();
        let (oprf_client_masked, secret_mask) = oprf_client_1::<32, Secp256k1, &[u8]>(username, password).unwrap();
        let server_response: DLEQProof<32, Secp256k1> = server(server_secret, oprf_client_masked.clone()).unwrap();
        let result = oprf_client_2(
            &AffinePoint::from_encoded(&oprf_client_masked).unwrap(),
            &secret_mask,
            &server_wrong_pubkey.to_affine(),
            &server_response,
        );
        assert!(result.is_err());
    }
    #[test]
    fn dleq_works() {
        let B = (AffinePoint::GENERATOR * Scalar::generate_vartime(&mut OsRng)).to_affine();
        let x = Scalar::generate_vartime(&mut OsRng);
        let pubkey = Secp256k1::base_point_or_generator().scalar_mul(&x);
        let proof: DLEQProof<32, Secp256k1> = DLEQProof::new(B, x).unwrap();
        assert!(proof.verify_and_get_output(&pubkey, &B).is_ok());
    }
    #[test]
    fn bad_dleq_does_not_work() {
        let B = (AffinePoint::GENERATOR * Scalar::generate_vartime(&mut OsRng)).to_affine();
        let x = Scalar::generate_vartime(&mut OsRng);
        let pubkey = B.scalar_mul(&x);
        let mut proof: DLEQProof<32, Secp256k1> = DLEQProof::new(B, x).unwrap();
        proof.response = Scalar::generate_vartime(&mut OsRng);
        assert!(proof.verify_and_get_output(&pubkey, &B).is_err());
    }
    #[test]
    fn secp256k1_point_to_field() {
        let scalar = Scalar::ZERO;
        let fieldel: F256k1 = F256k1::ZERO;
        let as_fieldel = F256k1::from(scalar);
        assert_eq!(as_fieldel, fieldel);
        let scalar = Scalar::ZERO - Scalar::ONE;
        let fieldel: F256k1 = F256k1::ZERO - F256k1::ONE;
        let as_fieldel = F256k1::from(scalar);
        assert_eq!(as_fieldel, fieldel);
    }
    #[test]
    fn secp256k1_field_to_point() {
        let scalar = Scalar::ZERO;
        let fieldel: F256k1 = F256k1::ZERO;
        let as_sc = Scalar::from(fieldel);
        assert_eq!(as_sc, scalar);
        let scalar = Scalar::ZERO - Scalar::ONE;
        let fieldel: F256k1 = F256k1::ZERO - F256k1::ONE;
        let as_sc = Scalar::from(fieldel);
        assert_eq!(as_sc, scalar);
    }
}
