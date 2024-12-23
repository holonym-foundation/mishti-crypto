//! Contains modules to use serde wiht points and scalars
use serde::{de::Error as DeErr, Deserialize, Deserializer, Serializer};
pub mod point_hex {
    use super::*;
    use crate::PointTrait;
    pub fn serialize<S, T, X>(point: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: PointTrait<X>,
    {
        let bytes = point.encode();
        serializer.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D, T, X>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: PointTrait<X>,
    {
        let s: &str = Deserialize::deserialize(deserializer)?;
        T::from_encoded(&hex::decode(s).map_err(|_| D::Error::custom(""))?).map_err(|_| D::Error::custom("error deserializing point"))
    }
}
pub mod scalar_hex {
    use super::*;
    use crate::ScalarTrait;
    pub fn serialize<S, T>(scalar: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: ScalarTrait,
    {
        let bytes = scalar.to_bytes();
        serializer.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: ScalarTrait,
    {
        let s: &str = Deserialize::deserialize(deserializer)?;
        T::from_bytes(&hex::decode(s).map_err(|_| D::Error::custom(""))?).map_err(|_| D::Error::custom("error deserializing point"))
    }
}
