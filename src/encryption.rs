use crate::{
    curve::{BabyJubJub, PointTrait, ScalarTrait},
    hash256,
    schnorrsig::{SchnorrSig, SchnorrSignable},
    serialization, Curve, Error,
};
use ark_ec::{twisted_edwards::Affine, AffineRepr};
use ark_ed_on_bn254::EdwardsConfig;
use ark_ff::PrimeField;
use ethers::types::Address;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::{iter::repeat, ops::Neg};
/// An El Gamal ciphertext is two points:
/// - ``ephemeral_dh_pubkey`` an ephemeral public key the sender cretes for Diffie-Hellman protocol between the sender and recipient's public key
/// - ``encrypted_msg`` the original message in point format, added to the shared secret of the Diffie-Hellman protocol with the sender and recipient
#[derive(Clone, Serialize, Deserialize)]
pub struct ElGamalCiphertext<const N: usize, C: Curve<N>> {
    #[serde(with = "serialization::point_hex")]
    pub encrypted_msg: C::Point,
    #[serde(with = "serialization::point_hex")]
    pub ephemeral_dh_pubkey: C::Point,
}
/// A signature of a decryption contract, from the ephemeral public key that was revealed in the ElGamal encryption (as the "c1" point)
#[derive(Clone, Serialize, Deserialize)]
pub struct DecryptionContractSignature {
    pub contract: Address,
    // #[serde(with = "serialization::point_hex")]
    // elgamal_ephemeral_pubkey: <BabyJubJub as Curve<32>>::Point,
    pub sig: SchnorrSig<32, BabyJubJub>,
}
/// The ciphertext along with the signed conditions that must be met to decrypt it
/// The conditions should be signed with the ephemeral public key from the ElGamal encryption
#[derive(Clone, Serialize, Deserialize)]
pub struct ElGamalCiphertextWithSignedConditions {
    pub ciphertext: ElGamalCiphertext<32, BabyJubJub>,
    pub signed_conditions: DecryptionContractSignature,
}
impl ElGamalCiphertextWithSignedConditions {
    fn _verify(&self) -> Result<(), Error> { <BabyJubJub as Curve<32>>::Scalar::verify(self.signed_conditions.contract.as_bytes(), &self.ciphertext.ephemeral_dh_pubkey, &self.signed_conditions.sig) }
    /// WARNING: this does not check the pubkey is the correct public key -- only that the signature of the contract from it is valid
    /// Such a check should still be done after calling this function
    pub fn get_contract_and_pubkey_if_valid(&self) -> Result<(Address, <BabyJubJub as Curve<32>>::Point), Error> {
        self._verify()?;
        Ok((self.signed_conditions.contract, self.ciphertext.ephemeral_dh_pubkey))
    }
}
pub trait MapCurve<const N: usize, C: Curve<N>> {
    /// How many bytes are used to increment the point
    const NUM_BYTES_PADDING: usize;
    fn koblitz_map(bytes: &[u8; N - Self::NUM_BYTES_PADDING]) -> Result<C::Point, Error>;
    fn reverse_koblitz(point: &C::Point) -> Result<[u8; N - Self::NUM_BYTES_PADDING], Error>;
}
impl MapCurve<32, BabyJubJub> for BabyJubJub {
    /// Allow 8 bytes for padding so there is a relatively low chance (2^-(64-1-3)) of failure to map to the curve
    /// the -1 is for the padding and -3 is for the subgroup
    /// Note this has some wraparoudn where for very high and thus very unlikely values, the point will wraparound
    const NUM_BYTES_PADDING: usize = 8;
    fn koblitz_map(bytes: &[u8; 24]) -> Result<<BabyJubJub as Curve<32>>::Point, Error> {
        let mut acc = 0u64;
        // One bit of 0 padding ensures that the y-coordinate never exceed the modulus
        while acc <= (u64::MAX >> 1) {
            // this likely does not need a hash but hashing feels sligthly safer than a clever alternative
            let deterministic_random_bit = hash256(bytes).first().unwrap() as &u8 % 2 == 0;
            // It's important the accumulator is first here so the y-coordinate is always less than the modulus
            let mut y = acc.to_be_bytes().to_vec();
            y.extend_from_slice(bytes);
            let point = Affine::<EdwardsConfig>::get_point_from_y_unchecked(BigUint::from_bytes_be(&y).into(), deterministic_random_bit);
            let succ = match point {
                Some(p) => p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve(),
                None => false,
            };
            if succ {
                return Ok(point.unwrap());
            } else {
                acc += 1;
            }
        }
        Err(Error::InvalidInput)
    }
    fn reverse_koblitz(point: &<BabyJubJub as Curve<32>>::Point) -> Result<[u8; 32 - Self::NUM_BYTES_PADDING], Error> {
        if !(point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve()) {
            return Err(Error::InvalidInput);
        }
        let (_, y) = AffineRepr::xy(point).ok_or(Error::InvalidInput)?;
        let big: BigUint = y.into_bigint().into(); //0.0[1..].try_into().unwrap();
        let bigbytes = big.to_bytes_be();
        let padding = 32 - bigbytes.len();
        debug_assert!(bigbytes.len() <= 32, "this should never occur");
        let mut bytes = repeat(0).take(padding).collect::<Vec<u8>>();
        bytes.extend_from_slice(&bigbytes);
        Ok(bytes[8..32].try_into().unwrap())
        // This won't panic
    }
}
pub fn encrypt_elgamal<const N: usize, C: Curve<N> + MapCurve<N, C>>(
    msg: &[u8; N - C::NUM_BYTES_PADDING],
    recipient_pubkey: &C::Point,
    custom_secret: Option<&C::Scalar>,
) -> Result<ElGamalCiphertext<N, C>, Error> {
    let msg_as_point = C::koblitz_map(msg)?;
    let default_ephem_secret = C::Scalar::rand_vartime();
    let ephem_secret = custom_secret.unwrap_or(&default_ephem_secret);
    let ephemeral_dh_pubkey = C::base_point_or_generator().scalar_mul(ephem_secret);
    let shared_secret_dh = recipient_pubkey.scalar_mul(ephem_secret);
    let encrypted_msg = shared_secret_dh.add_self(&msg_as_point);
    Ok(ElGamalCiphertext { encrypted_msg, ephemeral_dh_pubkey })
}
/// This takes a shared secret (e.g. one returned from Mishti network) and subtracts it from the encrypted message to retrieve the original message
pub fn decrypt_elgamal_from_shared_secret<const N: usize, C: Curve<N> + MapCurve<N, C>>(
    ciphertext: &ElGamalCiphertext<N, C>,
    shared_secret: &C::Point,
) -> Result<[u8; N - C::NUM_BYTES_PADDING], Error> {
    Ok(C::reverse_koblitz(&ciphertext.encrypted_msg.add_self(&shared_secret.clone().neg()))?)
}
/// Encrypts a message using ElGamal, then signs the conditions with the ephemeral public key used in the encryption
pub fn encrypt_with_conditions(msg: &[u8; 24], recipient_pubkey: &<BabyJubJub as Curve<32>>::Point, conditions_contract: Address) -> Result<ElGamalCiphertextWithSignedConditions, Error> {
    let secret = <BabyJubJub as Curve<32>>::Scalar::rand_vartime();
    let ciphertext = encrypt_elgamal(msg, recipient_pubkey, Some(&secret))?;
    let signed = secret.sign(conditions_contract.as_bytes());
    Ok(ElGamalCiphertextWithSignedConditions {
        ciphertext,
        signed_conditions: DecryptionContractSignature {
            contract: conditions_contract,
            sig: signed,
        },
    })
}
/// To be deleted. Allows choosing a custom secret for testing
pub fn testfn(
    msg: &[u8; 24],
    recipient_pubkey: &<BabyJubJub as Curve<32>>::Point,
    conditions_contract: Address,
    secret: <BabyJubJub as Curve<32>>::Scalar,
) -> Result<ElGamalCiphertextWithSignedConditions, Error> {
    let ciphertext = encrypt_elgamal(msg, recipient_pubkey, Some(&secret))?;
    let signed = secret.sign(conditions_contract.as_bytes());
    Ok(ElGamalCiphertextWithSignedConditions {
        ciphertext,
        signed_conditions: DecryptionContractSignature {
            contract: conditions_contract,
            sig: signed,
        },
    })
}
#[cfg(test)]
mod test {
    use super::*;
    use rand::{thread_rng, Rng};
    #[test]
    fn koblitz_encode_decode() {
        for _ in 0..100 {
            let mut msg = [0u8; 24];
            thread_rng().fill(&mut msg);
            let pt = BabyJubJub::koblitz_map(&msg).unwrap();
            assert_eq!(msg, BabyJubJub::reverse_koblitz(&pt).unwrap())
        }
    }
    #[test]
    fn encrypt_decrypt() {
        let msg = [0, 1, 123, 234, 69, 69, 128, 255, 0, 1, 2, 3, 4, 5, 6, 99, 01, 123, 45, 67, 0, 0, 1, 0u8];
        let recipient_secret_key = <BabyJubJub as Curve<32>>::Scalar::rand_vartime();
        let recipient_pubkey = BabyJubJub::base_point_or_generator().scalar_mul(&recipient_secret_key);
        let encrypted = encrypt_elgamal::<32, BabyJubJub>(&msg, &recipient_pubkey, None).unwrap();
        // This is intended to be computed by the network's scalar mul on the client's (possibly blinded) DH pubkey it sends but here we treat the recipient as the whole network
        let shared_secret = encrypted.ephemeral_dh_pubkey.scalar_mul(&recipient_secret_key);
        let decrypted = decrypt_elgamal_from_shared_secret(&encrypted, &shared_secret).unwrap();
        assert_eq!(msg, decrypted);
    }
}
