//! Converts between twisted and untwisted BabyJubJub coordinates using the mapping given by https://eprint.iacr.org/2008/013.pdf

//! BabyJubJub Twisted Edwards' a = 168700
//! sqrt(a) = 7214280148105020021932206872019688659210616427216992810330019057549499971851
//! 1 / sqrt(a) = 2957874849018779266517920829765869116077630550401372566248359756137677864698  
// use lazy_static::lazy_static;
use crate::{BabyJubJub, Curve};
use ark_ec::CurveConfig;
use ark_ed_on_bn254::EdwardsConfig;
use lazy_static::lazy_static;
use num_bigint::BigUint;
use std::str::FromStr;
lazy_static! {
    pub static ref SQRT_A: <EdwardsConfig as CurveConfig>::BaseField = BigUint::from_str("7214280148105020021932206872019688659210616427216992810330019057549499971851").unwrap().into();
    pub static ref SQRT_A_INV: <EdwardsConfig as CurveConfig>::BaseField = BigUint::from_str("2957874849018779266517920829765869116077630550401372566248359756137677864698").unwrap().into();
}
pub trait TwistedEdwardsConversion {
    fn edwards_to_twisted(&self) -> Self;
    fn twisted_to_edwards(&self) -> Self;
}
impl TwistedEdwardsConversion for <BabyJubJub as Curve<32>>::Point {
    fn twisted_to_edwards(&self) -> Self { Self { x: self.x * *SQRT_A, y: self.y } }
    fn edwards_to_twisted(&self) -> Self { Self { x: self.x * *SQRT_A_INV, y: self.y } }
}
#[cfg(test)]
mod test {
    use crate::{twisted_conversion::TwistedEdwardsConversion, BabyJubJub, Curve, PointTrait};
    use ark_ec::twisted_edwards::Affine;
    use ark_ed_on_bn254::EdwardsConfig;
    use ark_ff::UniformRand;
    use rand::rngs::ThreadRng;
    #[test]
    fn twist_untwist() {
        let a = Affine::<EdwardsConfig>::rand(&mut ThreadRng::default());
        let b = a.clone().edwards_to_twisted().twisted_to_edwards();
        assert_eq!(a, b);
        assert!(BabyJubJub::base_point_or_generator().is_on_curve());
        println!("Generator: {:?}", BabyJubJub::base_point_or_generator());
        println!("Generator twisted: {:?}", BabyJubJub::base_point_or_generator().edwards_to_twisted());
    }
}
