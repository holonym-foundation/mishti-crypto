use crate::{
    curve::{Curve, PointTrait, ScalarTrait},
    polynomial::{feldman_vss, lagrange_basis_at_0, verify_vss, Polynomial},
    resharing::ResharingError,
    Error,
};
use ff::Field;
use ff::PrimeField;
use num_bigint::BigUint;
use rand::thread_rng;
use rsa::{Pkcs1v15Encrypt, RsaPrivateKey, RsaPublicKey};
use std::{collections::HashMap, fmt};
use thiserror::Error;
use tracing::info;
#[derive(Error, Debug)]
pub enum DKGError {
    #[error("RSA Error")]
    RsaError(String),

    #[error("Failed to generate a key: {0}")]
    KeyGenerationFailed(String),

    #[error("Public keys not verified - step 16")]
    PublicKeyVerificationFailed,

    #[error("Error: {0}")]
    Other(String),

    #[error("Resharing Error: {0}")]
    ResharingError(#[from] ResharingError),
}
#[derive(Clone)]
pub struct Node<const N: usize, C: Curve<N>> {
    pub id: u128,
    pub rsa_pubkey: RsaPublicKey,
    pub rsa_seckey: RsaPrivateKey,
    pub init_pub_share: C::Point,
    pub private_share: C::FieldEl,
    pub network_pubkey: C::Point,
    pub own_partial_share: C::FieldEl,
}
#[derive(Error, Debug, Clone)]
pub struct Network {
    pub threshold: usize,
    pub total_nodes: usize,
    pub public_keys: HashMap<u128, RsaPublicKey>,
}
impl fmt::Display for Network {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Network {{ threshold: {}, total_nodes: {}, public_keys: [", self.threshold, self.total_nodes)?;
        for (id, key) in &self.public_keys {
            write!(f, "({}, {:?}), ", id, key)?;
        }
        write!(f, "] }}")
    }
}
impl Network {
    pub fn new(t: usize, n: usize) -> Result<Self, Error> {
        let set: HashMap<u128, RsaPublicKey> = HashMap::new();
        Ok(Self {
            threshold: t,
            total_nodes: n,
            public_keys: set,
        })
    }
    pub fn add_node<const N: usize, C: Curve<N>>(&mut self, no: &Node<N, C>) { self.public_keys.entry(no.id).or_insert(no.rsa_pubkey.clone()); }
}
impl<const N: usize, C: Curve<N>> Node<N, C> {
    pub fn new(id: u128) -> Result<Self, DKGError> {
        let mut rng = rand::thread_rng();
        let bits = 2048;
        let rsa_seckey = RsaPrivateKey::new(&mut rng, bits).map_err(|_e| DKGError::KeyGenerationFailed("RSA secret key for  node".to_string()))?;
        let rsa_pubkey = RsaPublicKey::from(&rsa_seckey);
        Ok(Self {
            id,
            rsa_pubkey,
            rsa_seckey,
            init_pub_share: C::ZERO,
            private_share: C::FieldEl::random(&mut thread_rng()),
            network_pubkey: C::ZERO,
            own_partial_share: C::FieldEl::random(&mut thread_rng()),
        })
    }
    pub fn with_rsa_key(id: u128, rsa_seckey: RsaPrivateKey) -> Result<Self, DKGError> {
        let rsa_pubkey = RsaPublicKey::from(&rsa_seckey);
        Ok(Self {
            id,
            rsa_pubkey,
            rsa_seckey,
            init_pub_share: C::ZERO,
            private_share: C::FieldEl::random(&mut thread_rng()),
            network_pubkey: C::ZERO,
            own_partial_share: C::FieldEl::random(&mut thread_rng()),
        })
    }
    /// Node i performs the first round of the distributed key generation (DKG) process, which includes the following steps:
    ///
    /// **Step 1**: Generates a random field element `ai0`.
    ///
    /// **Step 2**: Generates a random polynomial `fi` with `ai0` as free-term.
    ///
    /// **Step 3**: Utilizes Feldman's verifiable secret sharing (VSS) to distribute partial shares of `fi` among network participants, generating `y` and polynomial commitment `v`.
    ///
    /// **Step 5**: Encrypts the partial shares for each other node using RSA encryption and aggregates them to `y_ct`.
    ///
    /// **Step 6**: Stores its own partial share (`self.id`) from `y` and broadcast the encrypted partial shares `y_ct`and the polynomial commitment `v``.
    pub fn dkg_round_1(&self, network: &Network) -> Result<(HashMap<u128, Vec<u8>>, Vec<C::Point>, C::FieldEl), DKGError> {
        // Step 1
        let ai0 = C::FieldEl::random(&mut thread_rng());
        // Step 2
        let fi = Polynomial::<C::FieldEl>::random_polynomials_with_secret(network.threshold - 1, ai0);
        // Step 3
        let (y, v) = feldman_vss::<N, C, RsaPublicKey>(fi, &network.public_keys, network.threshold);
        // Step 5
        let mut rng = thread_rng();
        let mut y_ct: HashMap<u128, Vec<u8>> = HashMap::new();
        for (key, value) in network.public_keys.iter() {
            if *key != self.id {
                let ct = value
                    .encrypt(
                        &mut rng,
                        Pkcs1v15Encrypt,
                        y.get(key).ok_or_else(|| DKGError::Other(format!("Computed Polynomial not found for {}", key)))?.to_repr().as_ref(),
                    )
                    .map_err(|e| DKGError::RsaError(format!("Failed to encrypt the y_i: {}", e)))?;
                y_ct.insert(*key, ct);
            }
        }
        // Step 6
        let yii = *y.get(&self.id).ok_or(DKGError::Other(format!("Computed Polynomial not found for {}", self.id)))?;
        Ok((y_ct, v, yii))
    }
    /// Node i performs the second round of the distributed key generation (DKG) process, which includes the following steps:
    ///
    /// **Step 8**: Decrypts encrypted values, converts them to scalars, and constructs a hashmap `y` with all its partial shares.
    ///
    /// **Step 9**: Verifies the validity of values in `y` and `input_v` using a verifiable secret sharing (VSS) scheme.
    ///
    /// **Step 10**: Computes the master public key `K` as the sum of each node's secret's public key.
    ///
    /// **Step 11**: Computes the sum of the partial shares from `y` and stores it as `ki` the secret share.
    ///
    /// **Step 12**: Computes `Ki` its respective public key.
    ///
    /// **Step 13**: Broadcast its public key `Ki` and stores its private share `ki` and the master public key `K`.
    pub fn dkg_round_2(&self, network: &Network, input_y: HashMap<u128, Vec<u8>>, input_v: HashMap<u128, Vec<C::Point>>) -> Result<(C::FieldEl, C::Point, C::Point), DKGError> {
        assert!(input_v.len() == network.total_nodes - 1 && input_y.len() == network.total_nodes - 1, "dkg round 2 inputs not correct");
        for (_, j) in input_v.iter() {
            assert!(j.len() == network.threshold, "dkg round 2 inputs not correct");
        }
        // Step 8
        let mut y: HashMap<u128, <C as Curve<N>>::FieldEl> = HashMap::new();
        for (key, value) in input_y.iter() {
            let m = self
                .rsa_seckey
                .decrypt(Pkcs1v15Encrypt, value)
                .map_err(|_e| DKGError::RsaError("Failed to Decrypt the encrypted value".to_string()))?;
            let scalar = C::Scalar::from_biguint_vartime(BigUint::from_bytes_be(&m)).map_err(|_| DKGError::Other("Failed to convert to Scalar".to_string()))?;
            let c = C::FieldEl::from(scalar);
            y.entry(*key).or_insert(c);
        }
        // Step 9
        for (key, _value) in y.iter() {
            let eval = *y.get(key).ok_or(DKGError::Other("Eval not found".to_string()))?;
            if let Some(input_v_value) = input_v.get(key) {
                if !verify_vss::<N, C>(self.id, eval, input_v_value) {
                    return Err(DKGError::Other("VSS not verified - step 9".to_string()));
                }
            } else {
                return Err(DKGError::Other("Input VSS value not found".to_string()));
            }
        }
        // Step 10
        let K = input_v.values().fold(self.init_pub_share.clone(), |acc, x| acc.add_self(&x[0]));
        info!("DKG Group public key :{:?}", hex::encode(K.encode()));
        // Step11
        let ki = y.values().fold(self.own_partial_share, |acc, x| acc + x);
        // Step 12
        let Ki = C::base_point_or_generator().scalar_mul(&ki.into());
        // Step 13
        Ok((ki, Ki, K))
    }
    /// Node i performs the third round of the distributed key generation (DKG) process, which includes the following steps:
    ///
    /// **Step 15**: Computes the Lagrange interpolations `lambda_j` for each node.
    ///
    /// **Step 16**: Verifies that each node's public key attached to its Lagrange interpolation value corresponds to the master public key `K`.
    ///
    pub fn dkg_round_3(&self, network: &Network, Kj: &HashMap<u128, C::Point>) -> Result<C::Point, DKGError> {
        assert!(Kj.len() == network.total_nodes, "dkg round 3 inputs not correct");
        // Step 15
        let indices: Vec<u32> = network.public_keys.keys().map(|key| *key as u32).collect();
        let lambda: HashMap<u128, C::FieldEl> = network.public_keys.iter().fold(HashMap::new(), |mut acc, (key, _value)| {
            acc.entry(*key).or_insert(lagrange_basis_at_0(*key as u32, &indices));
            acc
        });
        // Step 16
        let res = lambda.iter().try_fold(C::ZERO, |acc, (key, value)| {
            Kj.get(key).ok_or_else(|| DKGError::Other("Key not found".to_string())).map(|K_j| {
                let temp = K_j.scalar_mul(&(*value).into());
                acc.add_self(&temp)
            })
        })?;
        assert!(res == self.network_pubkey, "public keys not verified - step 16");
        info!("DKG round 3 completed successfully");
        Ok(res)
    }
}
#[cfg(test)]
mod test {
    use super::*;
    use crate::{F256k1, Secp256k1};
    use k256::Scalar;
    #[test]
    fn test_rsa_encryption() {
        let mut rng = rand::thread_rng();
        let bits = 2048;
        let priv_key = RsaPrivateKey::new(&mut rng, bits).expect("failed to generate a key");
        let pub_key = RsaPublicKey::from(&priv_key);
        let x = F256k1::random(&mut thread_rng());
        let m: Vec<u8> = x.to_repr().0.try_into().unwrap();
        let enc = pub_key.encrypt(&mut rng, Pkcs1v15Encrypt, &m).expect("failed to encrypt");
        let dec = priv_key.decrypt(Pkcs1v15Encrypt, &enc).expect("failed to decrypt");
        let scalar = Scalar::from_str_vartime(&BigUint::from_bytes_be(&dec).to_string()).unwrap();
        let c = F256k1::from(scalar);
        assert!(x == c)
    }
    #[test]
    fn test_feldman_vss() {
        // We test for N={1, 2, 3} and t=2
        let set: HashMap<u128, _> = HashMap::from([(1, 0), (2, 0), (3, 0)]);
        let sec = F256k1::random(&mut thread_rng());
        let fi = Polynomial::<F256k1>::random_polynomials_with_secret(2, sec);
        let (y, v) = feldman_vss::<32, Secp256k1, _>(fi, &set, 3);
        assert!(
            verify_vss::<32, Secp256k1>(1, *y.get(&1).unwrap(), &v) & verify_vss::<32, Secp256k1>(2, *y.get(&2).unwrap(), &v) & verify_vss::<32, Secp256k1>(3, *y.get(&3).unwrap(), &v),
            "VSS not verified"
        );
    }
    #[test]
    fn test_feldman_vss_incorrect() {
        // We test for N={1, 2, 3} and t=2 with incorrect indexes for verification
        let set: HashMap<u128, _> = HashMap::from([(1, 0), (2, 0), (3, 0)]);
        let sec = F256k1::random(&mut thread_rng());
        let fi = Polynomial::<F256k1>::random_polynomials_with_secret(2, sec);
        let (y, v) = feldman_vss::<32, Secp256k1, _>(fi, &set, 3);
        assert!(
            !verify_vss::<32, Secp256k1>(1, *y.get(&2).unwrap(), &v) | !verify_vss::<32, Secp256k1>(5, *y.get(&2).unwrap(), &v) | !verify_vss::<32, Secp256k1>(3, *y.get(&1).unwrap(), &v),
            "VSS wrongly verified"
        );
    }
    #[test]
    fn test_full_2_3_dkg() {
        // We test a full DKG protocol for t=2 and n=3
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut threshold = Network::new(2, 3).unwrap();
        threshold.add_node(&n1);
        threshold.add_node(&n3);
        threshold.add_node(&n2);
        let (y1, v1, y11) = &n1.dkg_round_1(&threshold).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&threshold).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&threshold).unwrap();
        n1.own_partial_share = *y11;
        n1.init_pub_share = v1[0];
        n2.own_partial_share = *y22;
        n2.init_pub_share = v2[0];
        n3.own_partial_share = *y33;
        n3.init_pub_share = v3[0];
        let mut input_y1: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v1: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y1.insert(n2.id, y2.get(&n1.id).unwrap().clone());
        input_y1.insert(n3.id, y3.get(&n1.id).unwrap().clone());
        input_v1.insert(n2.id, v2.to_vec());
        input_v1.insert(n3.id, v3.to_vec());
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n3.id, y3.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n3.id, v3.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        let (k1, K1, K_1) = &n1.dkg_round_2(&threshold, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&threshold, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&threshold, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let _ = n1.dkg_round_3(&threshold, &K_set);
        let _ = n2.dkg_round_3(&threshold, &K_set);
        let _ = n3.dkg_round_3(&threshold, &K_set);
    }
    #[test]
    #[should_panic = "public keys not verified - step 16"]
    fn test_full_5_3_dkg() {
        // We test a full DKG protocol for t=5 and n=3 and is supposed to panic at step 16
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut threshold = Network::new(5, 3).unwrap();
        threshold.add_node(&n1);
        threshold.add_node(&n2);
        threshold.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&threshold).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&threshold).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&threshold).unwrap();
        n1.own_partial_share = *y11;
        n1.init_pub_share = v1[0];
        n2.own_partial_share = *y22;
        n2.init_pub_share = v2[0];
        n3.own_partial_share = *y33;
        n3.init_pub_share = v3[0];
        let mut input_y1: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v1: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y1.insert(n2.id, y2.get(&n1.id).unwrap().clone());
        input_y1.insert(n3.id, y3.get(&n1.id).unwrap().clone());
        input_v1.insert(n2.id, v2.to_vec());
        input_v1.insert(n3.id, v3.to_vec());
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n3.id, y3.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n3.id, v3.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        let (k1, K1, K) = &n1.dkg_round_2(&threshold, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K;
        let (k2, K2, K) = &n2.dkg_round_2(&threshold, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K;
        let (k3, K3, K) = &n3.dkg_round_2(&threshold, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let _ = n1.dkg_round_3(&threshold, &K_set);
        let _ = n2.dkg_round_3(&threshold, &K_set);
        let _ = n3.dkg_round_3(&threshold, &K_set);
    }
    #[test]
    fn test_full_3_10_dkg() {
        // We test a full DKG protocol for t=3 and n=10
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut n5: Node<32, Secp256k1> = Node::new(5).unwrap();
        let mut n6: Node<32, Secp256k1> = Node::new(6).unwrap();
        let mut n7: Node<32, Secp256k1> = Node::new(7).unwrap();
        let mut n8: Node<32, Secp256k1> = Node::new(8).unwrap();
        let mut n9: Node<32, Secp256k1> = Node::new(9).unwrap();
        let mut n10: Node<32, Secp256k1> = Node::new(10).unwrap();
        let mut threshold = Network::new(3, 10).unwrap();
        threshold.add_node(&n1);
        threshold.add_node(&n2);
        threshold.add_node(&n3);
        threshold.add_node(&n4);
        threshold.add_node(&n5);
        threshold.add_node(&n6);
        threshold.add_node(&n7);
        threshold.add_node(&n8);
        threshold.add_node(&n9);
        threshold.add_node(&n10);
        let (y1, v1, y11) = &n1.dkg_round_1(&threshold).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&threshold).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&threshold).unwrap();
        let (y4, v4, y44) = &n4.dkg_round_1(&threshold).unwrap();
        let (y5, v5, y55) = &n5.dkg_round_1(&threshold).unwrap();
        let (y6, v6, y66) = &n6.dkg_round_1(&threshold).unwrap();
        let (y7, v7, y77) = &n7.dkg_round_1(&threshold).unwrap();
        let (y8, v8, y88) = &n8.dkg_round_1(&threshold).unwrap();
        let (y9, v9, y99) = &n9.dkg_round_1(&threshold).unwrap();
        let (y10, v10, y1010) = &n10.dkg_round_1(&threshold).unwrap();
        n1.own_partial_share = *y11;
        n1.init_pub_share = v1[0];
        n2.own_partial_share = *y22;
        n2.init_pub_share = v2[0];
        n3.own_partial_share = *y33;
        n3.init_pub_share = v3[0];
        n4.own_partial_share = *y44;
        n4.init_pub_share = v4[0];
        n5.own_partial_share = *y55;
        n5.init_pub_share = v5[0];
        n6.own_partial_share = *y66;
        n6.init_pub_share = v6[0];
        n7.own_partial_share = *y77;
        n7.init_pub_share = v7[0];
        n8.own_partial_share = *y88;
        n8.init_pub_share = v8[0];
        n9.own_partial_share = *y99;
        n9.init_pub_share = v9[0];
        n10.own_partial_share = *y1010;
        n10.init_pub_share = v10[0];
        let mut input_y1: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v1: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y1.insert(n2.id, y2.get(&n1.id).unwrap().clone());
        input_y1.insert(n3.id, y3.get(&n1.id).unwrap().clone());
        input_y1.insert(n4.id, y4.get(&n1.id).unwrap().clone());
        input_y1.insert(n5.id, y5.get(&n1.id).unwrap().clone());
        input_y1.insert(n6.id, y6.get(&n1.id).unwrap().clone());
        input_y1.insert(n7.id, y7.get(&n1.id).unwrap().clone());
        input_y1.insert(n8.id, y8.get(&n1.id).unwrap().clone());
        input_y1.insert(n9.id, y9.get(&n1.id).unwrap().clone());
        input_y1.insert(n10.id, y10.get(&n1.id).unwrap().clone());
        input_v1.insert(n2.id, v2.to_vec());
        input_v1.insert(n3.id, v3.to_vec());
        input_v1.insert(n4.id, v4.to_vec());
        input_v1.insert(n5.id, v5.to_vec());
        input_v1.insert(n6.id, v6.to_vec());
        input_v1.insert(n7.id, v7.to_vec());
        input_v1.insert(n8.id, v8.to_vec());
        input_v1.insert(n9.id, v9.to_vec());
        input_v1.insert(n10.id, v10.to_vec());
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n3.id, y3.get(&n2.id).unwrap().clone());
        input_y2.insert(n4.id, y4.get(&n2.id).unwrap().clone());
        input_y2.insert(n5.id, y5.get(&n2.id).unwrap().clone());
        input_y2.insert(n6.id, y6.get(&n2.id).unwrap().clone());
        input_y2.insert(n7.id, y7.get(&n2.id).unwrap().clone());
        input_y2.insert(n8.id, y8.get(&n2.id).unwrap().clone());
        input_y2.insert(n9.id, y9.get(&n2.id).unwrap().clone());
        input_y2.insert(n10.id, y10.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n3.id, v3.to_vec());
        input_v2.insert(n4.id, v4.to_vec());
        input_v2.insert(n5.id, v5.to_vec());
        input_v2.insert(n6.id, v6.to_vec());
        input_v2.insert(n7.id, v7.to_vec());
        input_v2.insert(n8.id, v8.to_vec());
        input_v2.insert(n9.id, v9.to_vec());
        input_v2.insert(n10.id, v10.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_y3.insert(n4.id, y4.get(&n3.id).unwrap().clone());
        input_y3.insert(n5.id, y5.get(&n3.id).unwrap().clone());
        input_y3.insert(n6.id, y6.get(&n3.id).unwrap().clone());
        input_y3.insert(n7.id, y7.get(&n3.id).unwrap().clone());
        input_y3.insert(n8.id, y8.get(&n3.id).unwrap().clone());
        input_y3.insert(n9.id, y9.get(&n3.id).unwrap().clone());
        input_y3.insert(n10.id, y10.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        input_v3.insert(n4.id, v4.to_vec());
        input_v3.insert(n5.id, v5.to_vec());
        input_v3.insert(n6.id, v6.to_vec());
        input_v3.insert(n7.id, v7.to_vec());
        input_v3.insert(n8.id, v8.to_vec());
        input_v3.insert(n9.id, v9.to_vec());
        input_v3.insert(n10.id, v10.to_vec());
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_y4.insert(n2.id, y2.get(&n4.id).unwrap().clone());
        input_y4.insert(n3.id, y3.get(&n4.id).unwrap().clone());
        input_y4.insert(n5.id, y5.get(&n4.id).unwrap().clone());
        input_y4.insert(n6.id, y6.get(&n4.id).unwrap().clone());
        input_y4.insert(n7.id, y7.get(&n4.id).unwrap().clone());
        input_y4.insert(n8.id, y8.get(&n4.id).unwrap().clone());
        input_y4.insert(n9.id, y9.get(&n4.id).unwrap().clone());
        input_y4.insert(n10.id, y10.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        input_v4.insert(n2.id, v2.to_vec());
        input_v4.insert(n3.id, v3.to_vec());
        input_v4.insert(n5.id, v5.to_vec());
        input_v4.insert(n6.id, v6.to_vec());
        input_v4.insert(n7.id, v7.to_vec());
        input_v4.insert(n8.id, v8.to_vec());
        input_v4.insert(n9.id, v9.to_vec());
        input_v4.insert(n10.id, v10.to_vec());
        let mut input_y5: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v5: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y5.insert(n1.id, y1.get(&n5.id).unwrap().clone());
        input_y5.insert(n2.id, y2.get(&n5.id).unwrap().clone());
        input_y5.insert(n3.id, y3.get(&n5.id).unwrap().clone());
        input_y5.insert(n4.id, y4.get(&n5.id).unwrap().clone());
        input_y5.insert(n6.id, y6.get(&n5.id).unwrap().clone());
        input_y5.insert(n7.id, y7.get(&n5.id).unwrap().clone());
        input_y5.insert(n8.id, y8.get(&n5.id).unwrap().clone());
        input_y5.insert(n9.id, y9.get(&n5.id).unwrap().clone());
        input_y5.insert(n10.id, y10.get(&n5.id).unwrap().clone());
        input_v5.insert(n1.id, v1.to_vec());
        input_v5.insert(n2.id, v2.to_vec());
        input_v5.insert(n3.id, v3.to_vec());
        input_v5.insert(n4.id, v4.to_vec());
        input_v5.insert(n6.id, v6.to_vec());
        input_v5.insert(n7.id, v7.to_vec());
        input_v5.insert(n8.id, v8.to_vec());
        input_v5.insert(n9.id, v9.to_vec());
        input_v5.insert(n10.id, v10.to_vec());
        let mut input_y6: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v6: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y6.insert(n1.id, y1.get(&n6.id).unwrap().clone());
        input_y6.insert(n2.id, y2.get(&n6.id).unwrap().clone());
        input_y6.insert(n3.id, y3.get(&n6.id).unwrap().clone());
        input_y6.insert(n4.id, y4.get(&n6.id).unwrap().clone());
        input_y6.insert(n5.id, y5.get(&n6.id).unwrap().clone());
        input_y6.insert(n7.id, y7.get(&n6.id).unwrap().clone());
        input_y6.insert(n8.id, y8.get(&n6.id).unwrap().clone());
        input_y6.insert(n9.id, y9.get(&n6.id).unwrap().clone());
        input_y6.insert(n10.id, y10.get(&n6.id).unwrap().clone());
        input_v6.insert(n1.id, v1.to_vec());
        input_v6.insert(n2.id, v2.to_vec());
        input_v6.insert(n3.id, v3.to_vec());
        input_v6.insert(n4.id, v4.to_vec());
        input_v6.insert(n5.id, v5.to_vec());
        input_v6.insert(n7.id, v7.to_vec());
        input_v6.insert(n8.id, v8.to_vec());
        input_v6.insert(n9.id, v9.to_vec());
        input_v6.insert(n10.id, v10.to_vec());
        let mut input_y7: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v7: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y7.insert(n1.id, y1.get(&n7.id).unwrap().clone());
        input_y7.insert(n2.id, y2.get(&n7.id).unwrap().clone());
        input_y7.insert(n3.id, y3.get(&n7.id).unwrap().clone());
        input_y7.insert(n4.id, y4.get(&n7.id).unwrap().clone());
        input_y7.insert(n5.id, y5.get(&n7.id).unwrap().clone());
        input_y7.insert(n6.id, y6.get(&n7.id).unwrap().clone());
        input_y7.insert(n8.id, y8.get(&n7.id).unwrap().clone());
        input_y7.insert(n9.id, y9.get(&n7.id).unwrap().clone());
        input_y7.insert(n10.id, y10.get(&n7.id).unwrap().clone());
        input_v7.insert(n1.id, v1.to_vec());
        input_v7.insert(n2.id, v2.to_vec());
        input_v7.insert(n3.id, v3.to_vec());
        input_v7.insert(n4.id, v4.to_vec());
        input_v7.insert(n5.id, v5.to_vec());
        input_v7.insert(n6.id, v6.to_vec());
        input_v7.insert(n8.id, v8.to_vec());
        input_v7.insert(n9.id, v9.to_vec());
        input_v7.insert(n10.id, v10.to_vec());
        let mut input_y8: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v8: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y8.insert(n1.id, y1.get(&n8.id).unwrap().clone());
        input_y8.insert(n2.id, y2.get(&n8.id).unwrap().clone());
        input_y8.insert(n3.id, y3.get(&n8.id).unwrap().clone());
        input_y8.insert(n4.id, y4.get(&n8.id).unwrap().clone());
        input_y8.insert(n5.id, y5.get(&n8.id).unwrap().clone());
        input_y8.insert(n6.id, y6.get(&n8.id).unwrap().clone());
        input_y8.insert(n7.id, y7.get(&n8.id).unwrap().clone());
        input_y8.insert(n9.id, y9.get(&n8.id).unwrap().clone());
        input_y8.insert(n10.id, y10.get(&n8.id).unwrap().clone());
        input_v8.insert(n1.id, v1.to_vec());
        input_v8.insert(n2.id, v2.to_vec());
        input_v8.insert(n3.id, v3.to_vec());
        input_v8.insert(n4.id, v4.to_vec());
        input_v8.insert(n5.id, v5.to_vec());
        input_v8.insert(n6.id, v6.to_vec());
        input_v8.insert(n7.id, v7.to_vec());
        input_v8.insert(n9.id, v9.to_vec());
        input_v8.insert(n10.id, v10.to_vec());
        let mut input_y9: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v9: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y9.insert(n1.id, y1.get(&n9.id).unwrap().clone());
        input_y9.insert(n2.id, y2.get(&n9.id).unwrap().clone());
        input_y9.insert(n3.id, y3.get(&n9.id).unwrap().clone());
        input_y9.insert(n4.id, y4.get(&n9.id).unwrap().clone());
        input_y9.insert(n5.id, y5.get(&n9.id).unwrap().clone());
        input_y9.insert(n6.id, y6.get(&n9.id).unwrap().clone());
        input_y9.insert(n7.id, y7.get(&n9.id).unwrap().clone());
        input_y9.insert(n8.id, y8.get(&n9.id).unwrap().clone());
        input_y9.insert(n10.id, y10.get(&n9.id).unwrap().clone());
        input_v9.insert(n1.id, v1.to_vec());
        input_v9.insert(n2.id, v2.to_vec());
        input_v9.insert(n3.id, v3.to_vec());
        input_v9.insert(n4.id, v4.to_vec());
        input_v9.insert(n5.id, v5.to_vec());
        input_v9.insert(n6.id, v6.to_vec());
        input_v9.insert(n7.id, v7.to_vec());
        input_v9.insert(n8.id, v8.to_vec());
        input_v9.insert(n10.id, v10.to_vec());
        let mut input_y10: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v10: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y10.insert(n1.id, y1.get(&n10.id).unwrap().clone());
        input_y10.insert(n2.id, y2.get(&n10.id).unwrap().clone());
        input_y10.insert(n3.id, y3.get(&n10.id).unwrap().clone());
        input_y10.insert(n4.id, y4.get(&n10.id).unwrap().clone());
        input_y10.insert(n5.id, y5.get(&n10.id).unwrap().clone());
        input_y10.insert(n6.id, y6.get(&n10.id).unwrap().clone());
        input_y10.insert(n7.id, y7.get(&n10.id).unwrap().clone());
        input_y10.insert(n8.id, y8.get(&n10.id).unwrap().clone());
        input_y10.insert(n9.id, y9.get(&n10.id).unwrap().clone());
        input_v10.insert(n1.id, v1.to_vec());
        input_v10.insert(n2.id, v2.to_vec());
        input_v10.insert(n3.id, v3.to_vec());
        input_v10.insert(n4.id, v4.to_vec());
        input_v10.insert(n5.id, v5.to_vec());
        input_v10.insert(n6.id, v6.to_vec());
        input_v10.insert(n7.id, v7.to_vec());
        input_v10.insert(n8.id, v8.to_vec());
        input_v10.insert(n9.id, v9.to_vec());
        let (k1, K1, K_1) = &n1.dkg_round_2(&threshold, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&threshold, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&threshold, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let (k4, K4, K_4) = &n4.dkg_round_2(&threshold, input_y4, input_v4).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        let (k5, K5, K_5) = &n5.dkg_round_2(&threshold, input_y5, input_v5).unwrap();
        n5.private_share = *k5;
        n5.network_pubkey = *K_5;
        let (k6, K6, K_6) = &n6.dkg_round_2(&threshold, input_y6, input_v6).unwrap();
        n6.private_share = *k6;
        n6.network_pubkey = *K_6;
        let (k7, K7, K_7) = &n7.dkg_round_2(&threshold, input_y7, input_v7).unwrap();
        n7.private_share = *k7;
        n7.network_pubkey = *K_7;
        let (k8, K8, K_8) = &n8.dkg_round_2(&threshold, input_y8, input_v8).unwrap();
        n8.private_share = *k8;
        n8.network_pubkey = *K_8;
        let (k9, K9, K_9) = &n9.dkg_round_2(&threshold, input_y9, input_v9).unwrap();
        n9.private_share = *k9;
        n9.network_pubkey = *K_9;
        let (k10, K10, K_10) = &n10.dkg_round_2(&threshold, input_y10, input_v10).unwrap();
        n10.private_share = *k10;
        n10.network_pubkey = *K_10;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        K_set.insert(n4.id, K4.clone());
        K_set.insert(n5.id, K5.clone());
        K_set.insert(n6.id, K6.clone());
        K_set.insert(n7.id, K7.clone());
        K_set.insert(n8.id, K8.clone());
        K_set.insert(n9.id, K9.clone());
        K_set.insert(n10.id, K10.clone());
        let _ = n1.dkg_round_3(&threshold, &K_set);
        let _ = n2.dkg_round_3(&threshold, &K_set);
        let _ = n3.dkg_round_3(&threshold, &K_set);
        let _ = n4.dkg_round_3(&threshold, &K_set);
        let _ = n5.dkg_round_3(&threshold, &K_set);
        let _ = n6.dkg_round_3(&threshold, &K_set);
        let _ = n7.dkg_round_3(&threshold, &K_set);
        let _ = n8.dkg_round_3(&threshold, &K_set);
        let _ = n9.dkg_round_3(&threshold, &K_set);
        let _ = n10.dkg_round_3(&threshold, &K_set);
    }
}
