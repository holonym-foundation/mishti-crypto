//! For creating zkInjectedMask proofs. These let you derive a key from the JWT in a way that can't be double-spend attacked by anyone who sees the JWT.
//! It does so via the 2HashDH OPRF construction with one modificatoin:
//! The client input JWT is revealed, so it is not exactly oblivious, and it is proven
//! that the masked point given is r*hashToCurve(uniqueString(JWT)) for a secret mask r.
//! The JWT has a claim injected with the value R = r*G
//!
//! Whenever the user submits the JWT, they also submit a point they would like the OPRF of
//! They prove this point is r*hashToCurve(uniqueString(JWT)) for a secret r that is the discrete logarithm of R.
//! The network responds as normal as long as the user has proven they has masked it with the discrete log of R
//! Thus, the network's response can only be unmaksed by the user who knows r, i.e. the frontend who requested the JWT
//!
//! For more information, see zkInjectedMask.md
use crate::{serialization, Curve, DLEQProof, PointTrait, ScalarTrait, Secp256k1};
use anyhow::anyhow;
use base64::prelude::{Engine, BASE64_URL_SAFE_NO_PAD};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::error::Error;
#[derive(Serialize, Deserialize)]
pub struct Mask<const N: usize, C: Curve<N>> {
    #[serde(with = "serialization::point_hex")]
    pub public_mask: C::Point,
    #[serde(with = "serialization::scalar_hex")]
    pub secret_mask: C::Scalar,
}
impl<const N: usize, C: Curve<N>> Mask<N, C> {
    pub fn new() -> Self {
        let secret_mask = C::Scalar::rand_vartime();
        let public_mask = C::base_point_or_generator().scalar_mul(&secret_mask);
        Mask { public_mask, secret_mask }
    }
}
impl<const N: usize, C: Curve<N>> Default for Mask<N, C> {
    fn default() -> Self { Self::new() }
}
#[derive(Serialize, Deserialize)]
pub struct MaskProof<const N: usize, C: Curve<N>>(pub DLEQProof<N, C>);
impl<const N: usize, C: Curve<N>> MaskProof<N, C> {
    /// `unique_str`: The unique string from the JWT, i.e. the important parts that will be hashed -- these are the same for the same (user, issuer, website) tuple but different when any of these values change.
    /// The unique string is in the format "frontend_domain,issuer,user_id"
    pub fn create(secret_mask: C::Scalar, unique_str: &str) -> Result<MaskProof<N, C>, Box<dyn Error>> {
        let _public_mask = C::base_point_or_generator().scalar_mul(&secret_mask);
        Ok(MaskProof(DLEQProof::new(C::hash_to_curve(unique_str.as_bytes())?, secret_mask)?))
    }
    /// `public_mask`: The value of r*G from the JWT
    /// `unique_str`: The unique string from the JWT, i.e. the important parts that will be hashed -- these are the same for the same (user, issuer, website) tuple but different when any of these values change.
    /// This unique string is in the format "frontend_domain,issuer,user_id".
    pub fn verify_and_get_output(&self, public_mask: &C::Point, unique_str: &str) -> Result<C::Point, anyhow::Error> {
        Ok(self.0.verify_and_get_output(public_mask, &C::hash_to_curve(unique_str.as_bytes())?)?)
    }
}
type SecpPoint = <Secp256k1 as Curve<32>>::Point;
type SecpScalar = <Secp256k1 as Curve<32>>::Scalar;
/// Takes the secret mask and the network's output, unmasking it to reveal the actual PRF of the input (like the last step of the OPRF)
/// Hashes to scalar after unmasking
pub fn invert_mask_and_obtain_prf(secret_mask: &SecpScalar, network_output: &SecpPoint) -> Result<Vec<u8>, anyhow::Error> {
    let inv = secret_mask.mul_inv();
    if inv.is_none().unwrap_u8() == 1 {
        return Err(anyhow::anyhow!("Could not invert mask"));
    }
    let unmasked = network_output.scalar_mul(&inv.unwrap());
    Ok(Secp256k1::hash_from_curve(unmasked).to_bytes_be())
}
/// Data sent by the frontend to the network
#[derive(Serialize, Deserialize)]
pub struct FrontendData<const N: usize, C: Curve<N>> {
    pub jwt: String,
    pub key_idx: usize,
    pub mask_proof: MaskProof<N, C>,
}
#[derive(Serialize, Deserialize, Debug)]
pub struct JWTClaims {
    pub iss: String,
    pub aud: Option<String>,
    pub azp: Option<String>,
    pub sub: String,
    pub pubmask: String,
    /// Salt optionally allows the user to "rotate" their key -- if their web account is temporarily compromised, they can derive a new key from it by changing the salt
    pub salt: Option<String>,
}
impl JWTClaims {
    /// Does not verify token, only decodes its claims
    pub fn from_raw_token_unchecked(token: &str) -> Result<Self, anyhow::Error> {
        let parts = token.split('.').collect::<Vec<&str>>();
        if parts.len() != 3 {
            return Err(anyhow!("Invalid JWT format"));
        };
        println!("Parts[1]: {:?}", parts[1]);
        let claims = BASE64_URL_SAFE_NO_PAD.decode(parts[1])?;
        println!("Claims 1: {:?}", String::from_utf8(claims.clone()));
        let claims: Value = serde_json::from_slice(&claims)?;
        let e = || anyhow!("JWT claim missing");
        println!("Claims: {:?}", claims);
        println!("Salt: {:?}", claims.get("salt"));
        // let f: impl Fn(&Value, &str) -> Result<String, anyhow::Error> = |claims: &Value, key: &str| claims.get(key).ok_or_else(e)?.as_str().ok_or_else(e)?.to_string()
        Ok(Self {
            iss: claims.get("iss").ok_or_else(e)?.as_str().ok_or_else(e)?.to_string(),
            aud: claims.get("aud").and_then(|v| v.as_str()).map(|v| v.to_string()),
            azp: claims.get("azp").and_then(|v| v.as_str()).map(|v| v.to_string()),
            sub: claims.get("sub").ok_or_else(e)?.as_str().ok_or_else(e)?.to_string(),
            pubmask: claims.get("pubmask").ok_or_else(e)?.as_str().ok_or_else(e)?.to_string(),
            salt: claims.get("salt").and_then(|v| v.as_str()).map(|v| v.to_string()),
        })
    }
    /// Returns the unique string representing the important claims, i.e. those unique and invariant for this (user, website, issuer) tuple
    pub fn unique_string(&self) -> Result<String, anyhow::Error> {
        // The domain the user logged in at should be the token's azp, if the token has azp
        // Otherwise it should be the token's aud
        let login_at_domain = self.azp.clone().or(self.aud.clone().or(None)).ok_or(anyhow!("JWT must include azp or aud"))?;
        // It is crucial this unique string is correct -- this is the unique string that will be fed into the PRF
        // It should be unique per (user, issuer, page the user gets JWT from) tuple. I.e.
        // - a different user should have a different unqiue string
        // - if the user gets the JWT with a different issuer (and therefore the different issuer's signature) it will not have the same unique string
        // - if the user gets the JWT from a idfferent website (i.e. sign in with google on scam site vs. on reliable site) it will not have hte same unique string
        Ok([login_at_domain, self.iss.clone(), self.sub.clone(), self.salt.clone().unwrap_or("mishti-default-salt".to_string())].join(","))
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unique_str_is_unique() {
        let claims1 = JWTClaims {
            iss: "iss1".to_string(),
            aud: Some("aud1".to_string()),
            azp: None,
            sub: "sub1".to_string(),
            pubmask: "pubmask".to_string(),
            salt: Some("salt".to_string())
        };
        let claims2 = JWTClaims {
            iss: "iss1".to_string(),
            aud: Some("aud2".to_string()),
            azp: None,
            sub: "sub1".to_string(),
            pubmask: "pubmask".to_string(),
            salt: Some("salt".to_string())
        };
        // Note: azp and aud are treated the same, and azp overrides aud if present
        let claims3 = JWTClaims {
            iss: "iss1".to_string(),
            aud: None,
            azp: Some("azp3".to_string()),
            sub: "sub1".to_string(),
            pubmask: "pubmask".to_string(),
            salt: Some("salt".to_string())
        };
        let claims4 = JWTClaims {
            iss: "iss1".to_string(),
            aud: Some("aud1".to_string()),
            azp: None,
            sub: "sub4".to_string(),
            pubmask: "pubmask".to_string(),
            salt: Some("salt".to_string())
        };
        let claims5 = JWTClaims {
            iss: "iss1".to_string(),
            aud: Some("aud1".to_string()),
            azp: None,
            sub: "sub1".to_string(),
            pubmask: "pubmask".to_string(),
            salt: None
        };
        assert_ne!(claims1.unique_string().unwrap(), claims2.unique_string().unwrap());
        assert_ne!(claims1.unique_string().unwrap(), claims3.unique_string().unwrap());
        assert_ne!(claims1.unique_string().unwrap(), claims4.unique_string().unwrap());
        assert_ne!(claims1.unique_string().unwrap(), claims5.unique_string().unwrap());
    }
    #[test]
    fn from_raw_token_unchecked() {
        let token = "eyJhbGciOiJSUzI1NiIsImNhdCI6ImNsX0I3ZDRQRDExMUFBQSIsImtpZCI6Imluc18yaG8yUUc5TGM4WjRFTGY3UkhzM3EyWWYxYzMiLCJ0eXAiOiJKV1QifQ.eyJhenAiOiJodHRwOi8vZWMyLTU0LTI0Ni0yNDktMTEwLmV1LXdlc3QtMS5jb21wdXRlLmFtYXpvbmF3cy5jb206MzAwMCIsImV4cCI6MTcyNDkzNDkzNCwiaWF0IjoxNzI0OTM0ODc0LCJpc3MiOiJodHRwczovL2hhbmR5LXF1YWlsLTg0LmNsZXJrLmFjY291bnRzLmRldiIsImp0aSI6Ijk3MDk0MTNiOTE3MjU0Y2Y2ZTUxIiwibmJmIjoxNzI0OTM0ODY0LCJwdWJtYXNrIjoiMDJkNDM1ZjgyYmExMjU2ZDNmZjY2NmFkMjQ5ZThhOTgzODUxZGFiYjdmZWMxNjI0ZjMzNWU5MmFjOTMxNDY3MzUyIiwic2FsdCI6ImFuLWV4YW1wbGUtc2FsdCIsInNpZCI6InNlc3NfMmxJZVZVdGJQTVZtbENqUGQ2RU1paklDamNUIiwic3ViIjoidXNlcl8yaG8zaVVlQlV2b3hXZE1kT2E3Rk5qYndKbnkifQ.P6pQssuzLfbwSjh85BctucS3iHOjzYmVoinZuXgYCW7vvcZZF7_rSZwbVtB36yge5Q-S-V_H41eMBtt50RlSIaTl4WS-W-GTiYsw83e_kpMQ1HulfNJX_cXFAd7gNFeRVL4ybRivnmH_lo3JLPJctuD9g6LkvYPipjEH8ijrD4AEl8ya3wjuoGSW2VoZSu8NLYyanK962Pl4gzmv6sJetNBf9Zymew3pqlBeeDMsO8Zy9KIW_swJzzJSQS8E1uxDgzQSUlT-D7G8htOLptxC4lkTJ0kXdoMUoJoD1NThvuJwhA0odw9VvTWuOR4ixm73MUvW5pOxB48iDkjyLg5Htw";
        let claims = JWTClaims::from_raw_token_unchecked(token);
        assert!(claims.is_ok());
    }
    #[test]
    fn mask_proof() {
        let mask = Mask::<32, Secp256k1>::new();
        let unique_str = "unique_str";
        let proof = MaskProof::<32, Secp256k1>::create(mask.secret_mask, unique_str).unwrap();
        let output = proof.verify_and_get_output(&mask.public_mask, unique_str).unwrap();
    }
    #[test]
    fn mask_proof_from_frontend() {
        // let token = "eyJhbGciOiJSUzI1NiIsImNhdCI6ImNsX0I3ZDRQRDExMUFBQSIsImtpZCI6Imluc18yaG8yUUc5TGM4WjRFTGY3UkhzM3EyWWYxYzMiLCJ0eXAiOiJKV1QifQ.eyJhenAiOiJodHRwOi8vZWMyLTU0LTI0Ni0yNDktMTEwLmV1LXdlc3QtMS5jb21wdXRlLmFtYXpvbmF3cy5jb206MzAwMCIsImV4cCI6MTcyMTE2MTg2OSwiaWF0IjoxNzIxMTYxODA5LCJpc3MiOiJodHRwczovL2hhbmR5LXF1YWlsLTg0LmNsZXJrLmFjY291bnRzLmRldiIsImp0aSI6ImY4N2E3ZGI0MTMxOGRkZDFlODc2IiwibmJmIjoxNzIxMTYxNzk5LCJwdWJtYXNrIjoiMDJkMWI5N2ViN2I3MGM3ZjlhMTIwZGFjNTkxOTdmNWFhODQzOWFlMjM4MWY3ZTFkNDU5YWQ2M2Y2YmY1M2M2YWUyIiwic2lkIjoic2Vzc18yakZKeDhxNWxhZ3phcFR5Q0VSQzRCemZOa1kiLCJzdWIiOiJ1c2VyXzJobzNpVWVCVXZveFdkTWRPYTdGTmpid0pueSJ9.Wd6DmUnwfaq0V1FDkb8FYM-bBT247fy3PeABi-fNvjKrGOnkFLSw25CFNXzCl1pQP3aKKsWAZVKhm-24P8KJSjxg5Cq1uXt8mwotFrGB3rNshWXYBY5sComoeHfe8sG_UxZJmi6-t-vrPT7Jp_yqlcz1h-kCc3r_BTPskU0O0ibTzVJa0YOBypC2UPC695nOTXsP-lWmlfXBpykhQfwDsnnH3DEy7x3cRxEOeHEIi6xRdTDSmZPDszthhInN_BOryFxA5cy-qrpUhMCl75iCOTYmNaw5lMSNG0Xt8c-CmUShawGaNLInem3vongf3YosgjMIvRi81W9S5YtT_ABU1g";
        // let claims = JWTClaims::from_raw_token_unchecked(token);
        let fedata: FrontendData<32, Secp256k1> = bincode::deserialize(&[
            182, 3, 0, 0, 0, 0, 0, 0, 101, 121, 74, 104, 98, 71, 99, 105, 79, 105, 74, 83, 85, 122, 73, 49, 78, 105, 73, 115, 73, 109, 78, 104, 100, 67, 73, 54, 73, 109, 78, 115, 88, 48, 73, 51, 90,
            68, 82, 81, 82, 68, 69, 120, 77, 85, 70, 66, 81, 83, 73, 115, 73, 109, 116, 112, 90, 67, 73, 54, 73, 109, 108, 117, 99, 49, 56, 121, 97, 71, 56, 121, 85, 85, 99, 53, 84, 71, 77, 52, 87,
            106, 82, 70, 84, 71, 89, 51, 85, 107, 104, 122, 77, 51, 69, 121, 87, 87, 89, 120, 89, 122, 77, 105, 76, 67, 74, 48, 101, 88, 65, 105, 79, 105, 74, 75, 86, 49, 81, 105, 102, 81, 46, 101,
            121, 74, 104, 101, 110, 65, 105, 79, 105, 74, 111, 100, 72, 82, 119, 79, 105, 56, 118, 90, 87, 77, 121, 76, 84, 85, 48, 76, 84, 73, 48, 78, 105, 48, 121, 78, 68, 107, 116, 77, 84, 69,
            119, 76, 109, 86, 49, 76, 88, 100, 108, 99, 51, 81, 116, 77, 83, 53, 106, 98, 50, 49, 119, 100, 88, 82, 108, 76, 109, 70, 116, 89, 88, 112, 118, 98, 109, 70, 51, 99, 121, 53, 106, 98, 50,
            48, 54, 77, 122, 65, 119, 77, 67, 73, 115, 73, 109, 86, 52, 99, 67, 73, 54, 77, 84, 99, 121, 77, 84, 69, 50, 77, 84, 103, 50, 79, 83, 119, 105, 97, 87, 70, 48, 73, 106, 111, 120, 78, 122,
            73, 120, 77, 84, 89, 120, 79, 68, 65, 53, 76, 67, 74, 112, 99, 51, 77, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 104, 104, 98, 109, 82, 53, 76, 88, 70, 49, 89,
            87, 108, 115, 76, 84, 103, 48, 76, 109, 78, 115, 90, 88, 74, 114, 76, 109, 70, 106, 89, 50, 57, 49, 98, 110, 82, 122, 76, 109, 82, 108, 100, 105, 73, 115, 73, 109, 112, 48, 97, 83, 73,
            54, 73, 109, 89, 52, 78, 50, 69, 51, 90, 71, 73, 48, 77, 84, 77, 120, 79, 71, 82, 107, 90, 68, 70, 108, 79, 68, 99, 50, 73, 105, 119, 105, 98, 109, 74, 109, 73, 106, 111, 120, 78, 122,
            73, 120, 77, 84, 89, 120, 78, 122, 107, 53, 76, 67, 74, 119, 100, 87, 74, 116, 89, 88, 78, 114, 73, 106, 111, 105, 77, 68, 74, 107, 77, 87, 73, 53, 78, 50, 86, 105, 78, 50, 73, 51, 77,
            71, 77, 51, 90, 106, 108, 104, 77, 84, 73, 119, 90, 71, 70, 106, 78, 84, 107, 120, 79, 84, 100, 109, 78, 87, 70, 104, 79, 68, 81, 122, 79, 87, 70, 108, 77, 106, 77, 52, 77, 87, 89, 51,
            90, 84, 70, 107, 78, 68, 85, 53, 89, 87, 81, 50, 77, 50, 89, 50, 89, 109, 89, 49, 77, 50, 77, 50, 89, 87, 85, 121, 73, 105, 119, 105, 99, 50, 108, 107, 73, 106, 111, 105, 99, 50, 86, 122,
            99, 49, 56, 121, 97, 107, 90, 75, 101, 68, 104, 120, 78, 87, 120, 104, 90, 51, 112, 104, 99, 70, 82, 53, 81, 48, 86, 83, 81, 122, 82, 67, 101, 109, 90, 79, 97, 49, 107, 105, 76, 67, 74,
            122, 100, 87, 73, 105, 79, 105, 74, 49, 99, 50, 86, 121, 88, 122, 74, 111, 98, 122, 78, 112, 86, 87, 86, 67, 86, 88, 90, 118, 101, 70, 100, 107, 84, 87, 82, 80, 89, 84, 100, 71, 84, 109,
            112, 105, 100, 48, 112, 117, 101, 83, 74, 57, 46, 87, 100, 54, 68, 109, 85, 110, 119, 102, 97, 113, 48, 86, 49, 70, 68, 107, 98, 56, 70, 89, 77, 45, 98, 66, 84, 50, 52, 55, 102, 121, 51,
            80, 101, 65, 66, 105, 45, 102, 78, 118, 106, 75, 114, 71, 79, 110, 107, 70, 76, 83, 119, 50, 53, 67, 70, 78, 88, 122, 67, 108, 49, 112, 81, 80, 51, 97, 75, 75, 115, 87, 65, 90, 86, 75,
            104, 109, 45, 50, 52, 80, 56, 75, 74, 83, 106, 120, 103, 53, 67, 113, 49, 117, 88, 116, 56, 109, 119, 111, 116, 70, 114, 71, 66, 51, 114, 78, 115, 104, 87, 88, 89, 66, 89, 53, 115, 67,
            111, 109, 111, 101, 72, 102, 101, 56, 115, 71, 95, 85, 120, 90, 74, 109, 105, 54, 45, 116, 45, 118, 114, 80, 84, 55, 74, 112, 95, 121, 113, 108, 99, 122, 49, 104, 45, 107, 67, 99, 51,
            114, 95, 66, 84, 80, 115, 107, 85, 48, 79, 48, 105, 98, 84, 122, 86, 74, 97, 48, 89, 79, 66, 121, 112, 67, 50, 85, 80, 67, 54, 57, 53, 110, 79, 84, 88, 115, 80, 45, 108, 87, 109, 108,
            102, 88, 66, 112, 121, 107, 104, 81, 102, 119, 68, 115, 110, 110, 72, 51, 68, 69, 121, 55, 120, 51, 99, 82, 120, 69, 79, 101, 72, 69, 73, 105, 54, 120, 82, 100, 84, 68, 83, 109, 90, 80,
            68, 115, 122, 116, 104, 104, 73, 110, 78, 95, 66, 79, 114, 121, 70, 120, 65, 53, 99, 121, 45, 113, 114, 112, 85, 104, 77, 67, 108, 55, 53, 105, 67, 79, 84, 89, 109, 78, 97, 119, 53, 108,
            77, 83, 78, 71, 48, 88, 116, 56, 99, 45, 67, 109, 85, 83, 104, 97, 119, 71, 97, 78, 76, 73, 110, 101, 109, 51, 118, 111, 110, 103, 102, 51, 89, 111, 115, 103, 106, 77, 73, 118, 82, 105,
            56, 49, 87, 57, 83, 53, 89, 116, 84, 95, 65, 66, 85, 49, 103, 0, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 48, 51, 99, 97, 55, 48, 102, 100, 100, 53, 53, 48, 56, 100, 53, 100, 99, 54,
            48, 102, 102, 54, 55, 53, 100, 50, 56, 98, 48, 52, 54, 100, 56, 54, 55, 53, 50, 101, 97, 97, 54, 55, 54, 102, 97, 54, 97, 98, 100, 50, 49, 100, 99, 52, 98, 97, 48, 100, 54, 99, 55, 100,
            54, 48, 99, 56, 66, 0, 0, 0, 0, 0, 0, 0, 48, 50, 57, 51, 98, 50, 57, 52, 50, 55, 55, 101, 55, 99, 57, 54, 101, 99, 55, 52, 100, 97, 56, 102, 50, 56, 55, 48, 48, 48, 101, 53, 53, 56, 50,
            102, 101, 51, 55, 49, 101, 100, 57, 101, 49, 99, 50, 49, 102, 100, 56, 48, 51, 54, 98, 50, 97, 48, 54, 54, 101, 102, 54, 101, 99, 57, 66, 0, 0, 0, 0, 0, 0, 0, 48, 51, 51, 55, 50, 48, 100,
            102, 54, 51, 98, 49, 48, 50, 99, 50, 54, 101, 100, 100, 52, 102, 56, 102, 97, 100, 57, 53, 53, 99, 55, 54, 97, 49, 102, 52, 51, 101, 55, 99, 48, 51, 52, 56, 98, 100, 100, 97, 54, 50, 48,
            53, 56, 48, 57, 56, 53, 100, 57, 51, 52, 101, 48, 98, 97, 102, 66, 0, 0, 0, 0, 0, 0, 0, 48, 50, 51, 101, 101, 57, 55, 101, 53, 53, 98, 99, 102, 50, 100, 56, 49, 54, 55, 57, 54, 100, 54,
            55, 51, 49, 52, 53, 48, 54, 55, 51, 49, 55, 57, 49, 53, 50, 102, 48, 49, 54, 54, 99, 57, 102, 98, 101, 55, 100, 99, 57, 57, 98, 56, 97, 56, 98, 56, 53, 56, 54, 50, 49, 52, 57, 66, 0, 0,
            0, 0, 0, 0, 0, 48, 50, 50, 99, 53, 53, 49, 53, 53, 100, 49, 56, 97, 49, 49, 48, 100, 53, 49, 102, 52, 97, 99, 102, 102, 53, 48, 100, 102, 51, 48, 50, 52, 100, 98, 51, 54, 97, 57, 99, 53,
            101, 97, 57, 52, 51, 102, 99, 49, 51, 99, 101, 102, 52, 101, 53, 50, 55, 100, 98, 100, 97, 49, 54, 102, 51, 64, 0, 0, 0, 0, 0, 0, 0, 98, 57, 50, 50, 52, 57, 97, 52, 99, 102, 55, 55, 51,
            99, 49, 52, 56, 48, 55, 101, 54, 49, 56, 49, 49, 55, 48, 48, 97, 99, 102, 54, 51, 48, 53, 98, 101, 53, 102, 54, 98, 53, 57, 57, 100, 50, 48, 49, 100, 48, 97, 54, 50, 55, 100, 51, 52, 52,
            48, 48, 97, 56, 55, 51, 64, 0, 0, 0, 0, 0, 0, 0, 102, 57, 97, 54, 48, 56, 98, 50, 97, 56, 56, 48, 102, 98, 55, 51, 48, 54, 102, 52, 102, 50, 101, 56, 55, 52, 102, 53, 102, 98, 99, 54, 53,
            53, 53, 49, 49, 51, 53, 49, 52, 49, 49, 49, 56, 57, 56, 56, 102, 100, 99, 57, 100, 56, 100, 53, 56, 99, 102, 55, 102, 48, 51, 99,
        ])
        .unwrap();
        let claims = JWTClaims::from_raw_token_unchecked(&fedata.jwt).unwrap();
        let res = fedata
            .mask_proof
            .verify_and_get_output(
                &<Secp256k1 as Curve<32>>::Point::from_encoded(&hex::decode(&claims.pubmask).unwrap()).unwrap(),
                &claims.unique_string().unwrap(),
            )
            .unwrap();
        todo!()
    }
    #[test]
    fn mask_serde() {
        let mask = Mask::<32, Secp256k1>::new();
        let mask_ser = serde_json::to_string(&mask).unwrap();
        let mask_de: Value = serde_json::from_str(&mask_ser).unwrap();
        let pubmask = mask_de.get("public_mask").unwrap().as_str().unwrap();
        let privmask = mask_de.get("secret_mask").unwrap().as_str().unwrap();
        assert_eq!(
            Secp256k1::base_point_or_generator().scalar_mul(&<Secp256k1 as Curve<32>>::Scalar::from_bytes(&hex::decode(privmask).unwrap()).unwrap()),
            <Secp256k1 as Curve<32>>::Point::from_encoded(&hex::decode(pubmask).unwrap()).unwrap()
        )
    }
}
