//! Traits and implementations for elliptic curves and their corresponding scalar fields
//! This is so we can do the OPRF / ElGamal on any curve such as BabyJubJub, not just Secp256k1.
use crate::{hash256, hash512, twisted_conversion::TwistedEdwardsConversion, Error, F256k1, F256k1Repr};
use ark_ec::{twisted_edwards::Affine, AffineRepr, CurveConfig};
use ark_ed_on_bn254::{EdwardsConfig, FqConfig, Fr, FrConfig};
use ark_ff::BigInteger;
use ark_ff::{BigInt, Field, Fp, MontBackend, PrimeField as OtherPrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::convert::From;
use ark_std::str::FromStr;
use ff::{
    derive::subtle::{Choice, CtOption},
    PrimeField,
};
use k256::{
    elliptic_curve::{
        group::prime::PrimeCurveAffine,
        sec1::{FromEncodedPoint, ToEncodedPoint},
    },
    AffinePoint, EncodedPoint, FieldBytes, Scalar,
};
use lazy_static::lazy_static;
use num_bigint::BigUint;
use rand::random;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};
use std::{
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
};
use tracing::error;
pub const SECP256K1_P: &[u8; 32] = &[
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFC, 0x2F,
];
pub const BABYJUBJUB_P: &[u8; 32] = &[
    0x30, 0x64, 0x4E, 0x72, 0xE1, 0x31, 0xA0, 0x29, 0xB8, 0x50, 0x45, 0xB6, 0x81, 0x81, 0x58, 0x5D, 0x28, 0x33, 0xE8, 0x48, 0x79, 0xB9, 0x70, 0x91, 0x43, 0xE1, 0xF5, 0x93, 0xF0, 0x00, 0x00, 0x01,
];
lazy_static! {
    pub static ref BABYJUB_BASE_POINT: Affine<EdwardsConfig> = {
        let x = BigUint::from_str("5299619240641551281634865583518297030282874472190772894086521144482721001553")
            .expect("Invalid x-coordinate")
            .into();
        let y = BigUint::from_str("16950150798460657717958625567821834550301663161624707787222815936182638968203")
            .expect("Invalid y-coordinate")
            .into();
        Affine::<EdwardsConfig> { x, y }.twisted_to_edwards()
    };
}
// pub const fn BABYJUBJUB_base_point_or_generator() -> Affine<EdwardsConfig> {
//     Affine {
//         x: Fp::<MontBackend<FqConfig, 4>, 4>(
//             BigInt::<4>::try_from(BigUint::from_str("19698561148652590122159747500897617769866003486955115824547446575314762165298").unwrap()).unwrap(),//BigInt([6472377509509295154, 16410064374334370893, 2108221045001065086, 3138161842686642915]),
//             PhantomData::<MontBackend<FqConfig, 4>>
//         ),
//         y: Fp::<MontBackend<FqConfig, 4>, 4>(
//             BigInt::<4>::try_from(BigUint::from_str("19298250018296453272277890825869354524455968081175474282777126169995084727839").unwrap()).unwrap(),//BigInt([14012664558248429087, 3061340632283930986, 10424967955126647670, 3074388600315977886]),
//             PhantomData::<MontBackend<FqConfig, 4>>
//         )
//     }
//     // Affine::<EdwardsConfig>::base_point_or_generator()
//     // Affine::<EdwardsConfig>::deserialize_compressed(&[31u8, 134, 26, 103, 44, 252, 118, 194, 106, 225, 192, 219, 21, 17, 124, 42, 118, 123, 39, 16, 31, 237, 172, 144, 158, 32, 88, 167, 36, 108, 170, 170].as_slice()).unwrap()
// }
/// Some behavior we need from scalars
pub trait ScalarTrait {
    /// Returns the point's multiplicative inverse
    fn mul_inv(&self) -> CtOption<Self>
    where
        Self: Sized;
    fn from_biguint_vartime(b: BigUint) -> Result<Self, Error>
    where
        Self: Sized;
    fn to_biguint_vartime(&self) -> BigUint;
    fn rand_vartime() -> Self;
    fn from_bytes(b: &[u8]) -> Result<Self, Error>
    where
        Self: Sized;
    fn to_bytes(&self) -> Vec<u8>;
}
impl ScalarTrait for Scalar {
    fn mul_inv(&self) -> CtOption<Self> { self.invert() }
    fn rand_vartime() -> Self { Scalar::generate_vartime(&mut OsRng) }
    fn from_biguint_vartime(b: BigUint) -> Result<Self, Error> { Scalar::from_str_vartime(&b.to_string()).ok_or(Error::InvalidInput) }
    fn to_biguint_vartime(&self) -> BigUint { BigUint::from_bytes_be(&self.to_bytes()) }
    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let pt = Self::from_repr(*FieldBytes::from_slice(bytes));
        if pt.is_some().unwrap_u8() == 1 {
            Ok(pt.unwrap())
        } else {
            Err(Error::InvalidInput)
        }
    }
    fn to_bytes(&self) -> Vec<u8> { self.to_repr().to_vec() }
}
impl ScalarTrait for Fr {
    fn mul_inv(&self) -> CtOption<Self> { CtOption::new(self.inverse().unwrap(), if self.is_zero() { Choice::from(0) } else { Choice::from(1) }) }
    fn rand_vartime() -> Self { Fr::from(random::<u32>()) }
    fn from_biguint_vartime(b: BigUint) -> Result<Self, Error> {
        Ok(Fr::from(b))
        // Scalar::from_str_vartime(&b.to_string()).ok_or(Error::InvalidInput)
    }
    fn to_biguint_vartime(&self) -> BigUint { self.into_bigint().into() }
    fn to_bytes(&self) -> Vec<u8> {
        let mut writer = Vec::new();
        if let Err(e) = self.0.serialize_compressed(&mut writer) {
            error!("Error occured while serializing for feild Fr :{:?}", e);
        };
        writer
    }
    fn from_bytes(b: &[u8]) -> Result<Self, Error> { Ok(Self(BigInt::<4>::deserialize_compressed(b).map_err(|_| Error::InvalidInput)?, PhantomData::<MontBackend<FrConfig, 4>>)) }
}
/// Some behavior we need from points
pub trait PointTrait<S>
where
    Self: Sized,
{
    fn scalar_mul(&self, other: &S) -> Self;
    /// safer version of scalar_mul which will only perform the multiplcation if the point is on the curve and in the subgroup
    fn safe_scalar_mul_with_curve_and_subgroup_checks(&self, other: &S) -> Result<Self, Error> {
        if self.is_on_curve() && self.is_in_subgroup_assuming_on_curve() {
            Ok(self.scalar_mul(other))
        } else {
            Err(Error::InvalidInput)
        }
    }
    fn is_on_curve(&self) -> bool;
    fn is_in_subgroup_assuming_on_curve(&self) -> bool;
    /// Encodes the point to a byte array
    fn encode(&self) -> Vec<u8>;
    /// Decodes the point from a byte array
    fn from_encoded(encoded: &[u8]) -> Result<Self, Error>
    where
        Self: Sized;
    /// Adds self to Self and returns Self
    fn add_self(&self, other: &Self) -> Self;
}
impl PointTrait<Scalar> for AffinePoint {
    fn add_self(&self, other: &Self) -> Self { (self.to_curve() + other.to_curve()).to_affine() }
    fn scalar_mul(&self, other: &Scalar) -> Self { (*self * other).to_affine() }
    fn is_on_curve(&self) -> bool {
        // Since k256 does not have a method for this, nor does it allow accessing the x and y values of a point,
        // it seems the only way is this hacky method of encoding it and decoding it. decoding will fail if it's not on the curve
        let encoded = self.to_encoded_point(false);
        let decoded = AffinePoint::from_encoded_point(&encoded);
        decoded.map(|p| (p == *self) as u8).unwrap_or(0) != 0
    }
    fn is_in_subgroup_assuming_on_curve(&self) -> bool {
        // always true since there is no cofactor
        true
    }
    fn encode(&self) -> Vec<u8> { self.to_encoded_point(true).as_bytes().into() }
    fn from_encoded(encoded: &[u8]) -> Result<Self, Error> {
        let p = AffinePoint::from_encoded_point(&EncodedPoint::from_bytes(encoded).map_err(|_| Error::InvalidInput)?);
        if p.is_some().unwrap_u8() == 1 {
            Ok(p.unwrap())
        } else {
            Err(Error::Other(String::from("Failed to parse EncodedPoint as SEC1-encoded AffinePoint")))
        }
    }
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncodedBabyJubJubPoint {
    pub greatest: bool,
    pub y: Vec<u8>,
}
impl PointTrait<Fr> for Affine<EdwardsConfig> {
    fn add_self(&self, other: &Self) -> Self { (*self + *other).into() }
    fn scalar_mul(&self, other: &Fr) -> Self { (*self * other).into() }
    fn is_on_curve(&self) -> bool { self.is_on_curve() }
    fn is_in_subgroup_assuming_on_curve(&self) -> bool { self.is_in_correct_subgroup_assuming_on_curve() }
    // Low priority fix: this will panic if the point is 0 due to the unwrap on get_xs_from_y_unchecked, or if it is not on the curve
    fn encode(&self) -> Vec<u8> {
        let (x, y) = AffineRepr::xy(self).unwrap();
        let options = Affine::<EdwardsConfig>::get_xs_from_y_unchecked(*y).unwrap();
        let mut ser = Vec::new();
        y.0.serialize_compressed(&mut ser).unwrap();
        let greatest;
        if options.0 == *x {
            greatest = false;
        } else if options.1 == *x {
            greatest = true;
        } else {
            panic!("Point not on curve");
        }
        // x.0.to_bytes_be()
        bincode::serialize(&EncodedBabyJubJubPoint { greatest, y: ser }).unwrap()
    }
    fn from_encoded(encoded: &[u8]) -> Result<Self, Error> {
        let encoded: EncodedBabyJubJubPoint = bincode::deserialize(encoded).unwrap();
        let y = Fp::<MontBackend<FqConfig, 4>, 4>(
            BigInt::<4>::deserialize_compressed(&*encoded.y).map_err(|_| Error::InvalidInput)?,
            PhantomData::<MontBackend<FqConfig, 4>>,
        );
        let point = Affine::<EdwardsConfig>::get_point_from_y_unchecked(y, encoded.greatest);
        if let Some(p) = point {
            if p.is_on_curve() {
                return Ok(p);
            }
        }
        Err(Error::InvalidInput)
    }
}
pub trait Curve<const N: usize> {
    type Point: Send
        + Sized
        + Sync
        + Clone
        + PartialEq
        + PointTrait<Self::Scalar>
        + Neg<Output = Self::Point>
        // If we try to work wiht a curve without Neg trait implemented for its point, we can just remove this line and add a neg() to PointTrait
        + std::fmt::Debug;
    // type AffinePoint: Mul<Self::Scalar, Output = Self::AffinePoint> + PartialEq;
    // type ProjectivePoint: Add;
    /// The representation of scalar elements in the field
    type Scalar: Mul<Self::Scalar, Output = Self::Scalar>
        + Sub<Self::Scalar, Output = Self::Scalar>
        + From<Self::FieldEl>
        + Clone
        + PartialEq
        + ScalarTrait
        + Add<Output = Self::Scalar>
        + Mul<Output = Self::Scalar>;
    /// The prime field of order of the curve's prime-order (sub)group. Could be the same as Self::Scalar but does not need to be (e.g. k256 has a scalar element that does not implement PrimeField)
    type FieldEl: PrimeField + From<Self::Scalar>;
    /// The name of the curve
    const NAME: &'static str;
    /// The modulus of the prime field of order of the curve's prime-order (sub)group, in big-endian bytes
    const FIELD_MODULUS_BE: [u8; N];
    /// The zero point
    const ZERO: Self::Point;
    /// The generator point, or subgroup base point if we should be working within a subgroup
    fn base_point_or_generator() -> Self::Point;
    /// Standard hash to curve such as Koblitz method or deterministic Elligator2
    fn hash_to_curve(msg: &[u8]) -> Result<Self::Point, Error>;
    /// Takes point from curve and converts to a uniform or negligably biased BigUint in 0..Self::Modulus
    fn hash_from_curve(point: Self::Point) -> BigUint;
}
impl From<Scalar> for F256k1 {
    fn from(value: Scalar) -> Self {
        let as_be_bytes = value.to_bytes().to_vec();
        let as_40_be_bytes = [vec![0; 40 - as_be_bytes.len()], as_be_bytes].concat();
        F256k1::from_repr(F256k1Repr(as_40_be_bytes.try_into().unwrap())).unwrap()
    }
}
impl From<F256k1> for Scalar {
    // If it's important this could be sped up by not converting to a bigint then string and then back to a scalar
    fn from(value: F256k1) -> Self {
        let as_be_bytes = value.to_repr().0.to_vec();
        Scalar::from_str_vartime(&BigUint::from_bytes_be(&as_be_bytes).to_string()).unwrap()
    }
}
impl From<Fr> for BABYJUBJUB {
    fn from(value: Fr) -> Self {
        let a: BigInt<4> = value.into_bigint();
        let as_be_bytes = a.to_bytes_be().to_vec();
        let mut as_40_be_bytes = [vec![0; 40 - as_be_bytes.len()], as_be_bytes].concat();
        let last_32_bytes = as_40_be_bytes.split_off(as_40_be_bytes.len() - 32);
        let val: [u8; 32] = last_32_bytes.try_into().expect("slice with incorrect length");
        BABYJUBJUB::from_repr(BABYJUBJUBRepr(val)).unwrap()
    }
}
impl From<BABYJUBJUB> for Fr {
    // If it's important this could be sped up by not converting to a bigint then string and then back to a scalar
    fn from(value: BABYJUBJUB) -> Self {
        let as_be_bytes = value.to_repr().0.to_vec();
        Fr::from_str(&BigUint::from_bytes_be(&as_be_bytes).to_string()).unwrap()
    }
}
#[derive(Clone, Serialize, Deserialize)]
pub struct Secp256k1;
impl Curve<32> for Secp256k1 {
    const NAME: &'static str = "Secp256k1";
    type Point = AffinePoint;
    // type ProjectivePoint = ProjectivePoint;
    type Scalar = Scalar;
    // this is pretty similar to Scalar, but the allows a different interface that Scalar does not necessarily allow
    type FieldEl = F256k1;
    const FIELD_MODULUS_BE: [u8; 32] = [
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
    ];
    const ZERO: Self::Point = AffinePoint::IDENTITY;
    fn base_point_or_generator() -> Self::Point { AffinePoint::GENERATOR }
    /// Method for hashing to curve similar to BLS paper https://www.iacr.org/archive/asiacrypt2001/22480516.pdf
    /// This is similar to the Koblitz way of encoding a message to a point where you take hash(m || n) and increment n until you get a valid x coordinate for a point on the curve
    /// This hashes m to a curve by taking hash1(n || m) and finding when the resulting value is a valid x-coordinate on the curve. It gets the y value by hash2(m)
    /// It is important that the hash function produces a curve point of which nobody knows the discrelete logarithm.
    /// It's probably also important the it produces a uniform random point on the curve, but I don't see right now why that would matter -- just generally good idea to avoid any mistakes later.
    /// Thus, hash1 has a 512 bit output which is taken mod p (not mod n) of secp256k1 -- x-coordinates are mod p even though order is n.
    /// Since an x-coordinate can correspond to two y-coordinates, a random bit is used from hash2(m || n) to determine which y-coordinate to use
    fn hash_to_curve(msg: &[u8]) -> Result<AffinePoint, Error> {
        let mut acc: u16 = 0;
        let acc_lt = 1024;
        while acc < acc_lt {
            // get hash(msg,acc)
            let mut concatted: Vec<u8> = acc.to_be_bytes().to_vec();
            concatted.extend_from_slice(msg);
            let digest = hash512(&concatted);
            // get a random bit (first byte of hash2(input) mod 2)
            let deterministic_random_bit = hash256(&concatted).first().ok_or(Error::InvalidInput)? as &u8 % 2;
            let xcoord = BigUint::from_bytes_be(&digest) % BigUint::from_bytes_be(SECP256K1_P);
            let mut encoded_point: [u8; 33] = [0; 33];
            encoded_point[0] = deterministic_random_bit + 2; // +2 maps from 0 to 2 and 1 to 3 to follow SEC1 encoding standard
            let xcoord_vec = xcoord.to_bytes_be();
            // pad with 0s if x coordinate is less than 32 bytes
            let bytes_under = 32 - xcoord_vec.len();
            encoded_point[1..1 + bytes_under].copy_from_slice(&vec![0; bytes_under]);
            // let xcoord_slice: [u8] = xcoord_vec.into(); // Should never error so ok to unwrap
            encoded_point[1 + bytes_under..33].copy_from_slice(&xcoord_vec);
            let encoded: EncodedPoint = EncodedPoint::from_bytes(encoded_point).map_err(|_| Error::UnknownError)?;
            let pt = AffinePoint::from_encoded_point(&encoded);
            let succ = pt.map(|p| (p.is_on_curve() && p.is_in_subgroup_assuming_on_curve()) as u8).unwrap_or(0);
            if succ == 1 {
                return Ok(pt.unwrap());
            } else {
                acc += 1
            }
        }
        Err(Error::ExtremelyRareErrorInputUnhashableToCurve)
    }
    fn hash_from_curve(point: Self::Point) -> BigUint {
        let hashed_512 = hash512(point.to_encoded_point(true).as_bytes());
        BigUint::from_bytes_be(&hashed_512) % BigUint::from_bytes_be(&Self::FIELD_MODULUS_BE)
    }
}
// /// For serde to be able to serialize and deserialize the point
// #[derive(Serialize, Deserialize)]
// #[serde(remote = "Affine")]
// pub struct AffineDef<P: TECurveConfig> {
//     /// X coordinate of the point represented as a field element
//     pub x: P::BaseField,
//     /// Y coordinate of the point represented as a field element
//     pub y: P::BaseField,
// }
#[derive(Clone, Serialize, Deserialize)]
pub struct BabyJubJub;
impl Curve<32> for BabyJubJub {
    const NAME: &'static str = "BabyJubJub";
    type Point = Affine<EdwardsConfig>;
    // type ProjectivePoint = ProjectivePoint;
    type Scalar = Fr;
    // this is pretty similar to Scalar, but the allows a different interface that Scalar does not necessarily allow
    type FieldEl = BABYJUBJUB;
    const FIELD_MODULUS_BE: [u8; 32] = [
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
    ];
    const ZERO: Self::Point = Affine::<EdwardsConfig>::new_unchecked(<EdwardsConfig as CurveConfig>::BaseField::ZERO, <EdwardsConfig as CurveConfig>::BaseField::ONE);
    fn base_point_or_generator() -> Self::Point { *BABYJUB_BASE_POINT }
    /// Note: not constant time
    fn hash_to_curve(msg: &[u8]) -> Result<Affine<EdwardsConfig>, Error> {
        let mut acc: u16 = 0;
        let acc_lt = 1024;
        while acc < acc_lt {
            // get hash(msg,acc)
            let mut concatted: Vec<u8> = acc.to_be_bytes().to_vec();
            concatted.extend_from_slice(msg);
            let digest = hash512(&concatted);
            // get a random bit (first byte of hash2(input) mod 2)
            let deterministic_random_bit = hash256(&concatted).first().ok_or(Error::InvalidInput)? as &u8 % 2 == 0;
            let xcoord = BigUint::from_bytes_be(&digest) % BigUint::from_bytes_be(BABYJUBJUB_P);
            let mut encoded_point: [u8; 32] = [0; 32];
            // encoded_point[0] = deterministic_random_bit + 2; // +2 maps from 0 to 2 and 1 to 3 to follow SEC1 encoding standard
            let xcoord_vec = xcoord.to_bytes_be();
            // pad with 0s if x coordinate is less than 32 bytes
            let bytes_under = 32 - xcoord_vec.len();
            encoded_point[..bytes_under].copy_from_slice(&vec![0; bytes_under]);
            // let xcoord_slice: [u8] = xcoord_vec.into(); // Should never error so ok to unwrap
            encoded_point[bytes_under..].copy_from_slice(&xcoord_vec);
            let encoded_and_formatted = bincode::serialize(&EncodedBabyJubJubPoint {
                greatest: deterministic_random_bit,
                y: encoded_point.into(),
            })
            .unwrap();
            let result = Self::Point::from_encoded(&encoded_and_formatted);
            let succ = match result {
                Ok(pt) => pt.is_on_curve() && pt.is_in_subgroup_assuming_on_curve(),
                _ => false,
            };
            if succ {
                return result;
            } else {
                acc += 1
            }
        }
        Err(Error::ExtremelyRareErrorInputUnhashableToCurve)
    }
    fn hash_from_curve(point: Self::Point) -> BigUint {
        let hashed_512 = hash512(point.encode());
        BigUint::from_bytes_be(&hashed_512) % BigUint::from_bytes_be(&Self::FIELD_MODULUS_BE)
    }
}
#[derive(PrimeField)]
#[PrimeFieldModulus = "2736030358979909402780800718157159386076813972158567259200215660948447373041"]
#[PrimeFieldGenerator = "31"]
#[PrimeFieldReprEndianness = "big"]
pub struct BABYJUBJUB([u64; 4]);
// Most tests for functions above are in lib.rs (and potentially other files) rather than here
#[cfg(test)]
mod test {
    use super::*;
    use ark_ff::{One, UniformRand};
    use ff::Field;
    use num_traits::FromPrimitive;
    use rand::{rngs::ThreadRng, thread_rng};
    // #[test]
    // fn test_babyjubjub_from_to_bigint() {
    //     let s = <BabyJubJub as Curve<32>>::Scalar::rand(&mut ThreadRng::default());
    //     assert_eq!(s, <BabyJubJub as Curve<32>>::Scalar::from_biguint_vartime(s.to_biguint_vartime()).unwrap());
    // }
    // #[test]
    // fn test_secp256k1_from_to_bigint() {
    //     todo!("test it works")
    // }
    #[test]
    /*
    3 :F256k1(0x000000000000000022b1e9052bbf99818bd28eaed98bb191d2bcd70c5c2251ee62a8ebeed29ce305),AffinePoint { x: FieldElement(FieldElementImpl { value: FieldElement5x52([3154543752933896, 3925070918837316, 1446283022857260, 3088770020216847, 129994489373615]), magnitude: 1, normalized: true }), y: FieldElement(FieldElementImpl { value: FieldElement5x52([3214320229027179, 2478192780968798, 4141307712916965, 3692816715497473, 67057109338326]), magnitude: 1, normalized: true }), infinity: 0 },AffinePoint { x: FieldElement(FieldElementImpl { value: FieldElement5x52([1699700903374584, 1683941591281988, 4373649247835164, 764892868887117, 210664654040143]), magnitude: 1, normalized: true }), y: FieldElement(FieldElementImpl { value: FieldElement5x52([1385971923103331, 2834501591051038, 313465328020421, 3906354048655036, 84183820624059]), magnitude: 1, normalized: true }), infinity: 0 }
     */
    fn test_secp256k1_scalar_to_from_bytes() {
        let p = Scalar::rand_vartime();
        assert_eq!(Scalar::from_bytes(&ScalarTrait::to_bytes(&p)).unwrap(), p);
    }
    #[test]
    fn test_babyjub_scalar_to_from_bytes() {
        let p = Fr::rand_vartime();
        assert_eq!(Fr::from_bytes(&p.to_bytes()).unwrap(), p);
    }
    #[test]
    fn test_babyjubjub_to_from_encoded() {
        let point = BabyJubJub::hash_to_curve(b"hello").unwrap();
        let encoded = point.encode();
        let point2 = <BabyJubJub as Curve<32>>::Point::from_encoded(&encoded).unwrap();
        assert_eq!(point, point2);
    }
    #[test]
    fn test_secp256k1_from_to_biguint() {
        let r = Scalar::rand_vartime();
        assert_eq!(r, Scalar::from_biguint_vartime(r.to_biguint_vartime()).unwrap());
    }
    #[test]
    fn test_babyjubjub_from_to_biguint() {
        let r = Fr::rand_vartime();
        assert_eq!(r, Fr::from_biguint_vartime(r.to_biguint_vartime()).unwrap());
    }
    #[test]
    fn test_secp256k1_on_curve() {
        // There is no way to produce an AffinePoint not on the curve so this test is somewhat pointless...
        for i in (0..100) {
            let p = Secp256k1::hash_to_curve(&vec![69, 69, i as u8]).unwrap();
            assert!(p.is_on_curve());
        }
    }
    #[test]
    fn test_bjj_on_curve() {
        for i in (0..100) {
            let p = BabyJubJub::hash_to_curve(&vec![69, 69, i as u8]).unwrap();
            assert!(p.is_on_curve());
            let mut bad = p.clone();
            bad.x.0 = bad.y.0.clone();
            assert!(!bad.is_on_curve());
        }
    }
    #[test]
    fn test_bjj_in_subgroup() {
        let not_in_subgroup = Affine::<EdwardsConfig> {
            x: BigUint::from_str("535593336793637676479053006008715741038479202311237693774606504536042252795").unwrap().into(),
            y: BigUint::from_str("23469575780919401").unwrap().into(),
        };
        for i in (0..100) {
            let p = BabyJubJub::hash_to_curve(&vec![69, 69, i as u8]).unwrap();
            assert!(p.is_in_subgroup_assuming_on_curve());
            // Multiplying the generator by an odd number should not be in the subgroup, but multiplying that by 8 should always be in the subgroup:
            let also_not_in_subgroup = not_in_subgroup.scalar_mul(&BigUint::from_u64((random::<u32>() as u64 * 2) + 1).unwrap().into());
            assert!(also_not_in_subgroup.is_on_curve() && !also_not_in_subgroup.is_in_subgroup_assuming_on_curve());
            let in_subgroup = also_not_in_subgroup.scalar_mul(&Fr::from(8));
            assert!(in_subgroup.is_on_curve() && in_subgroup.is_in_subgroup_assuming_on_curve());
        }
    }
}
