use crate::{
    curve::{Curve, PointTrait, ScalarTrait},
    dkg::{Network, Node},
    polynomial::{feldman_vss, lagrange_basis_at_0, verify_vss, Polynomial},
};
use ff::Field;
use ff::PrimeField;
use num_bigint::BigUint;
use rand::thread_rng;
use rsa::{Pkcs1v15Encrypt, RsaPublicKey};
use std::collections::HashMap;
use std::ops::Mul;
use thiserror::Error;
use tracing::info;
#[derive(Error, Debug)]
pub enum ResharingError {
    #[error("RSA Error")]
    RsaError(String),
    #[error("Failed to generate a key :{0}")]
    KeyGenerationFailed(String),
    #[error("public keys not verified - step 16")]
    PublicKeyVerificationFailed,
    #[error("Error: `{0}`")]
    Other(String),
}
impl<const N: usize, C: Curve<N>> Node<N, C> {
    /// Node i from the old quorum `Q_e` performs the first round of the resharing protocol, which includes the following steps:
    ///
    /// **Step 1**: Computes its Lagrange interpolation `lambda_i` based on the list of participating nodes.
    ///
    /// **Step 2**: Transforms its secret share `ki` with its `lambda_i` to an additive share `ai0`.
    ///
    /// **Step 3**: Generates a random polynomial `fi` with `ai0` as free-term.
    ///
    /// **Step 4**: Utilizes Feldman's verifiable secret sharing (VSS) to distribute partial shares of `fi` among network participants, generating `y` and polynomial commitment `v`.
    ///
    /// **Step 5**: Encrypts the partial shares for each other node using RSA encryption and aggregates them to `y_ct`.
    ///
    /// **Step 6**: Broadcast the encrypted partial shares `y_ct`and the polynomial commitment `v``.
    pub fn resharing_round_1(&self, t_star: &Network, new_quorum: &Network) -> Result<(HashMap<u128, Vec<u8>>, Vec<C::Point>), ResharingError> {
        // Step 1
        let indices: Vec<u32> = t_star.public_keys.keys().map(|key| *key as u32).collect();
        let lambda_i: C::FieldEl = lagrange_basis_at_0(self.id as u32, &indices);
        // Step 2
        let ai0 = self.private_share.mul(&lambda_i);
        // Step 3
        let fi = Polynomial::<C::FieldEl>::random_polynomials_with_secret(new_quorum.threshold - 1, ai0);
        // Step 4
        let (y, v) = feldman_vss::<N, C, RsaPublicKey>(fi, &new_quorum.public_keys, new_quorum.threshold);
        // Step 5
        let mut rng = thread_rng();
        let mut y_ct: HashMap<u128, Vec<u8>> = HashMap::new();
        for (key, value) in new_quorum.public_keys.iter() {
            let ct = value
                .encrypt(
                    &mut rng,
                    Pkcs1v15Encrypt,
                    y.get(key)
                        .ok_or_else(|| ResharingError::Other(format!("Computed Polynomial not found for {}", key)))?
                        .to_repr()
                        .as_ref(),
                )
                .map_err(|e| ResharingError::RsaError(format!("Failed to encrypt the y_i: {}", e)))?;
            y_ct.insert(*key, ct);
        }
        // Step 6
        Ok((y_ct, v))
    }
    /// Node i  from the new quorum `Q_e+1` performs the second round of the resharing protocol, which includes the following steps:
    ///
    /// **Step 8**: Decrypts encrypted values, converts them to scalars, and constructs a hashmap `y` with all its partial shares.
    ///
    /// **Step 9**: Verifies the validity of values in `y` and `input_v` using a verifiable secret sharing (VSS) scheme.
    ///
    /// **Step 10**: Computes the master public key `K` as the sum of each node's secret's public key and verifies it corresponds to the master public key from last epoch.
    ///
    /// **Step 11**: Computes the sum of the partial shares from `y` and stores it as `ki` the secret share.
    ///
    /// **Step 12**: Computes `Ki` its respective public key.
    ///
    /// **Step 13**: Broadcast its public key `Ki` and stores its private share `ki` and the master public key `K`.
    pub fn resharing_round_2(
        &self,
        t_star: &Network,
        new_quorum: &Network,
        input_y: HashMap<u128, Vec<u8>>,
        input_v: HashMap<u128, Vec<C::Point>>,
        K_dkg: C::Point,
    ) -> Result<(C::FieldEl, C::Point, C::Point), ResharingError> {
        assert!(input_v.len() == t_star.total_nodes && input_y.len() == t_star.total_nodes, "resharing round 2 inputs not correct");
        for (_, j) in input_v.iter() {
            info!("j.len() == new_quorum.threshold , {},{}", j.len(), new_quorum.threshold);
            assert!(j.len() == new_quorum.threshold, "resharing round 2 inputs not correct");
        }
        // Step 8
        let mut y: HashMap<u128, <C as Curve<N>>::FieldEl> = HashMap::new();
        for (key, value) in input_y.iter() {
            let m = self
                .rsa_seckey
                .decrypt(Pkcs1v15Encrypt, value)
                .map_err(|_e| ResharingError::RsaError("Failed to Decrypt the encrypted value".to_string()))?;
            let scalar = C::Scalar::from_biguint_vartime(BigUint::from_bytes_be(&m)).map_err(|_| ResharingError::Other("Failed to convert to Scalar".to_string()))?;
            let c = C::FieldEl::from(scalar);
            y.entry(*key).or_insert(c);
        }
        // Step 9
        for (key, _value) in y.iter() {
            let eval = *y.get(key).ok_or(ResharingError::Other("Eval not found".to_string()))?;
            if let Some(input_v_value) = input_v.get(key) {
                if !verify_vss::<N, C>(self.id, eval, input_v_value) {
                    return Err(ResharingError::Other("VSS not verified - step 9".to_string()));
                }
            } else {
                return Err(ResharingError::Other("Input VSS value not found".to_string()));
            }
        }
        // Step 10
        let K = input_v.values().fold(C::ZERO, |acc, x| acc.add_self(&x[0]));
        if K != K_dkg {
            return Err(ResharingError::Other("Group public key not verified - step 10".to_string()));
        }
        info!("Resharing Group public key :{:?}", hex::encode(K.encode()));
        // Step11
        let ki = y.values().fold(C::FieldEl::ZERO, |acc, x| acc + x);
        // Step 12
        let Ki = C::base_point_or_generator().scalar_mul(&ki.into());
        // Step 13
        Ok((ki, Ki, K))
    }
    /// Node i  from the new quorum `Q_e+1` performs the third round of the resharing protocol, which includes the following steps:
    ///
    /// **Step 15**: Computes the Lagrange interpolations `lambda_j` for each node.
    ///
    /// **Step 16**: Verifies that each node's public key attached to its Lagrange interpolation value corresponds to the master public key `K`.
    ///
    pub fn resharing_round_3(&self, network: &Network, Kj: &HashMap<u128, C::Point>) -> Result<C::Point, ResharingError> {
        assert!(Kj.len() == network.total_nodes, "resharing round 3 inputs not correct");
        // Step 15
        let indices: Vec<u32> = network.public_keys.keys().map(|key| *key as u32).collect();
        info!("Received network indexes round 3 :{:?}", indices);
        info!("Received Kj indexes round 3 :{:?}", Kj.keys().cloned().collect::<Vec<u128>>());
        let lambda: HashMap<u128, C::FieldEl> = network.public_keys.iter().fold(HashMap::new(), |mut acc, (key, _value)| {
            acc.entry(*key).or_insert(lagrange_basis_at_0(*key as u32, &indices));
            acc
        });
        // Step 16
        let res = lambda.iter().try_fold(C::ZERO, |acc, (key, value)| {
            Kj.get(key).ok_or_else(|| ResharingError::Other("Key not found".to_string())).map(|K_j| {
                let temp = K_j.scalar_mul(&(*value).into());
                acc.add_self(&temp)
            })
        })?;
        assert!(res == self.network_pubkey, "public keys not verified - step 16");
        info!("Resharing Round 3 completed successfully ");
        Ok(res)
    }
}
#[cfg(test)]
mod test {
    use super::*;
    use crate::Secp256k1;
    #[test]
    fn test_2_3_resharing() {
        // We first run a 2-out-of-3 DKG
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut old_quorum = Network::new(2, 3).unwrap();
        old_quorum.add_node(&n1);
        old_quorum.add_node(&n2);
        old_quorum.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&old_quorum).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&old_quorum).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&old_quorum).unwrap();
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
        let (k1, K1, K_1) = &n1.dkg_round_2(&old_quorum, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&old_quorum, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&old_quorum, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let K_dkg = n1.dkg_round_3(&old_quorum, &K_set).unwrap();
        let _ = n2.dkg_round_3(&old_quorum, &K_set);
        let _ = n3.dkg_round_3(&old_quorum, &K_set);
        // We create a set T* composed of n1 and n2
        let mut t_star = Network::new(2, 2).unwrap();
        t_star.add_node(&n1);
        t_star.add_node(&n2);
        // We create a new quorum with same t and n but composed of n2, n3 and n4
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut new_quorum = Network::new(2, 3).unwrap();
        new_quorum.add_node(&n2);
        new_quorum.add_node(&n3);
        new_quorum.add_node(&n4);
        // We run resharing round 1 on set T*
        let (y1, v1) = &n1.resharing_round_1(&t_star, &new_quorum).unwrap();
        let (y2, v2) = &n2.resharing_round_1(&t_star, &new_quorum).unwrap();
        // We run resharing round 2 on new_quorum composed of n2, n3 and n4
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n2.id, y2.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n2.id, v2.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_y4.insert(n2.id, y2.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        input_v4.insert(n2.id, v2.to_vec());
        let (k2, K2, K_2) = &n2.resharing_round_2(&t_star, &new_quorum, input_y2, input_v2, K_dkg).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.resharing_round_2(&t_star, &new_quorum, input_y3, input_v3, K_dkg).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let (k4, K4, K_4) = &n4.resharing_round_2(&t_star, &new_quorum, input_y4, input_v4, K_dkg).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        // We run resharing round 3 on new_quorum composed of n2, n3 and n4
        let mut K_set = HashMap::new();
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        K_set.insert(n4.id, K4.clone());
        let K_resharing = n2.resharing_round_3(&new_quorum, &K_set);
        let _ = n3.resharing_round_3(&new_quorum, &K_set);
        let _ = n4.resharing_round_3(&new_quorum, &K_set);
    }
    #[test]
    #[should_panic = "resharing round 2 inputs not correct"]
    fn test_2_3_resharing_bad_t_star() {
        // We first run a 2-out-of-3 DKG
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut old_quorum = Network::new(2, 3).unwrap();
        old_quorum.add_node(&n1);
        old_quorum.add_node(&n2);
        old_quorum.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&old_quorum).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&old_quorum).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&old_quorum).unwrap();
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
        let (k1, K1, K_1) = &n1.dkg_round_2(&old_quorum, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&old_quorum, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&old_quorum, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let K_dkg = n1.dkg_round_3(&old_quorum, &K_set).unwrap();
        let _ = n2.dkg_round_3(&old_quorum, &K_set);
        let _ = n3.dkg_round_3(&old_quorum, &K_set);
        // We create a bad set T* with lees elements than t from Q_e and composed of only n1
        let mut t_star = Network::new(2, 2).unwrap();
        t_star.add_node(&n1);
        // We create a new quorum with same t and n but composed of n2, n3 and n4
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut new_quorum = Network::new(2, 3).unwrap();
        new_quorum.add_node(&n2);
        new_quorum.add_node(&n3);
        new_quorum.add_node(&n4);
        // We run resharing round 1 on set T*
        let (y1, v1) = &n1.resharing_round_1(&t_star, &new_quorum).unwrap();
        // We run resharing round 2 on new quorum composed of n2, n3 and n4
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        let (k2, K2, K_2) = &n2.resharing_round_2(&t_star, &new_quorum, input_y2, input_v2, K_dkg).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.resharing_round_2(&t_star, &new_quorum, input_y3, input_v3, K_dkg).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let (k4, K4, K_4) = &n4.resharing_round_2(&t_star, &new_quorum, input_y4, input_v4, K_dkg).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        // We run resharing round 3 on new quorum composed of n2, n3 and n4
        let mut K_set = HashMap::new();
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        K_set.insert(n4.id, K4.clone());
        let K_resharing = n2.resharing_round_3(&new_quorum, &K_set);
        let _ = n3.resharing_round_3(&new_quorum, &K_set);
        let _ = n4.resharing_round_3(&new_quorum, &K_set);
    }
    #[test]
    fn test_2_3_resharing_disjoint_quorum() {
        // We first run a 2-out-of-3 DKG
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut old_quorum = Network::new(2, 3).unwrap();
        old_quorum.add_node(&n1);
        old_quorum.add_node(&n2);
        old_quorum.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&old_quorum).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&old_quorum).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&old_quorum).unwrap();
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
        let (k1, K1, K_1) = &n1.dkg_round_2(&old_quorum, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&old_quorum, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&old_quorum, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let K_dkg = n1.dkg_round_3(&old_quorum, &K_set).unwrap();
        let _ = n2.dkg_round_3(&old_quorum, &K_set);
        let _ = n3.dkg_round_3(&old_quorum, &K_set);
        // We create a set T* composed of n1 and n2
        let mut t_star = Network::new(2, 2).unwrap();
        t_star.add_node(&n1);
        t_star.add_node(&n2);
        // We create a new quorum disjoint from old_quorum with same t and n but composed of n4, n5 and n6
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut n5: Node<32, Secp256k1> = Node::new(5).unwrap();
        let mut n6: Node<32, Secp256k1> = Node::new(6).unwrap();
        let mut new_quorum = Network::new(2, 3).unwrap();
        new_quorum.add_node(&n4);
        new_quorum.add_node(&n5);
        new_quorum.add_node(&n6);
        // We run resharing round 1 on set T*
        let (y1, v1) = &n1.resharing_round_1(&t_star, &new_quorum).unwrap();
        let (y2, v2) = &n2.resharing_round_1(&t_star, &new_quorum).unwrap();
        // We run resharing round 2 on new quorum composed of n4, n5 and n6
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_y4.insert(n2.id, y2.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        input_v4.insert(n2.id, v2.to_vec());
        let mut input_y5: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v5: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y5.insert(n1.id, y1.get(&n5.id).unwrap().clone());
        input_y5.insert(n2.id, y2.get(&n5.id).unwrap().clone());
        input_v5.insert(n1.id, v1.to_vec());
        input_v5.insert(n2.id, v2.to_vec());
        let mut input_y6: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v6: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y6.insert(n1.id, y1.get(&n6.id).unwrap().clone());
        input_y6.insert(n2.id, y2.get(&n6.id).unwrap().clone());
        input_v6.insert(n1.id, v1.to_vec());
        input_v6.insert(n2.id, v2.to_vec());
        let (k4, K4, K_4) = &n4.resharing_round_2(&t_star, &new_quorum, input_y4, input_v4, K_dkg).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        let (k5, K5, K_5) = &n5.resharing_round_2(&t_star, &new_quorum, input_y5, input_v5, K_dkg).unwrap();
        n5.private_share = *k5;
        n5.network_pubkey = *K_5;
        let (k6, K6, K_6) = &n6.resharing_round_2(&t_star, &new_quorum, input_y6, input_v6, K_dkg).unwrap();
        n6.private_share = *k6;
        n6.network_pubkey = *K_6;
        // We run resharing round 3 on new quorum composed of n4, n5 and n6
        let mut K_set = HashMap::new();
        K_set.insert(n4.id, K4.clone());
        K_set.insert(n5.id, K5.clone());
        K_set.insert(n6.id, K6.clone());
        let K_resharing = n4.resharing_round_3(&new_quorum, &K_set);
        let _ = n5.resharing_round_3(&new_quorum, &K_set);
        let _ = n6.resharing_round_3(&new_quorum, &K_set);
    }
    #[test]
    fn test_2_3_into_3_3_resharing() {
        // We first run a 2-out-of-3 DKG
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut old_quorum = Network::new(2, 3).unwrap();
        old_quorum.add_node(&n1);
        old_quorum.add_node(&n2);
        old_quorum.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&old_quorum).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&old_quorum).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&old_quorum).unwrap();
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
        let (k1, K1, K_1) = &n1.dkg_round_2(&old_quorum, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&old_quorum, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&old_quorum, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let K_dkg = n1.dkg_round_3(&old_quorum, &K_set).unwrap();
        let _ = n2.dkg_round_3(&old_quorum, &K_set);
        let _ = n3.dkg_round_3(&old_quorum, &K_set);
        // We create a set T* composed of n1 and n2
        let mut t_star = Network::new(2, 2).unwrap();
        t_star.add_node(&n1);
        t_star.add_node(&n2);
        // We create a new quorum with a different t and same n composed of n2, n3 and n4
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut new_quorum = Network::new(3, 3).unwrap();
        new_quorum.add_node(&n2);
        new_quorum.add_node(&n3);
        new_quorum.add_node(&n4);
        // We run resharing round 1 on set T*
        let (y1, v1) = &n1.resharing_round_1(&t_star, &new_quorum).unwrap();
        let (y2, v2) = &n2.resharing_round_1(&t_star, &new_quorum).unwrap();
        // We run resharing round 2 on new quorum composed of n2, n3 and n4
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n2.id, y2.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n2.id, v2.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_y4.insert(n2.id, y2.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        input_v4.insert(n2.id, v2.to_vec());
        let (k2, K2, K_2) = &n2.resharing_round_2(&t_star, &new_quorum, input_y2, input_v2, K_dkg).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.resharing_round_2(&t_star, &new_quorum, input_y3, input_v3, K_dkg).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let (k4, K4, K_4) = &n4.resharing_round_2(&t_star, &new_quorum, input_y4, input_v4, K_dkg).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        // We run resharing round 3 on new quorum composed of n2, n3 and n4
        let mut K_set = HashMap::new();
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        K_set.insert(n4.id, K4.clone());
        let K_resharing = n2.resharing_round_3(&new_quorum, &K_set);
        let _ = n3.resharing_round_3(&new_quorum, &K_set);
        let _ = n4.resharing_round_3(&new_quorum, &K_set);
    }
    #[test]
    fn test_2_3_into_2_4_resharing() {
        // We first run a 2-out-of-3 DKG
        let mut n1: Node<32, Secp256k1> = Node::new(1).unwrap();
        let mut n2: Node<32, Secp256k1> = Node::new(2).unwrap();
        let mut n3: Node<32, Secp256k1> = Node::new(3).unwrap();
        let mut old_quorum = Network::new(2, 3).unwrap();
        old_quorum.add_node(&n1);
        old_quorum.add_node(&n2);
        old_quorum.add_node(&n3);
        let (y1, v1, y11) = &n1.dkg_round_1(&old_quorum).unwrap();
        let (y2, v2, y22) = &n2.dkg_round_1(&old_quorum).unwrap();
        let (y3, v3, y33) = &n3.dkg_round_1(&old_quorum).unwrap();
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
        let (k1, K1, K_1) = &n1.dkg_round_2(&old_quorum, input_y1, input_v1).unwrap();
        n1.private_share = *k1;
        n1.network_pubkey = *K_1;
        let (k2, K2, K_2) = &n2.dkg_round_2(&old_quorum, input_y2, input_v2).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.dkg_round_2(&old_quorum, input_y3, input_v3).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let mut K_set = HashMap::new();
        K_set.insert(n1.id, K1.clone());
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        let K_dkg = n1.dkg_round_3(&old_quorum, &K_set).unwrap();
        let _ = n2.dkg_round_3(&old_quorum, &K_set);
        let _ = n3.dkg_round_3(&old_quorum, &K_set);
        // We create a set T* composed of n1 and n2
        let mut t_star = Network::new(2, 2).unwrap();
        t_star.add_node(&n1);
        t_star.add_node(&n2);
        // We create a new quorum with same t but a different n composed of n2, n3, n4 and n5
        let mut n4: Node<32, Secp256k1> = Node::new(4).unwrap();
        let mut n5: Node<32, Secp256k1> = Node::new(5).unwrap();
        let mut new_quorum = Network::new(2, 4).unwrap();
        new_quorum.add_node(&n2);
        new_quorum.add_node(&n3);
        new_quorum.add_node(&n4);
        new_quorum.add_node(&n5);
        // We run resharing round 1 on set T*
        let (y1, v1) = &n1.resharing_round_1(&t_star, &new_quorum).unwrap();
        let (y2, v2) = &n2.resharing_round_1(&t_star, &new_quorum).unwrap();
        // We run resharing round 2 on new_quorum composed of n2, n3, n4 and n5
        let mut input_y2: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v2: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y2.insert(n1.id, y1.get(&n2.id).unwrap().clone());
        input_y2.insert(n2.id, y2.get(&n2.id).unwrap().clone());
        input_v2.insert(n1.id, v1.to_vec());
        input_v2.insert(n2.id, v2.to_vec());
        let mut input_y3: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v3: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y3.insert(n1.id, y1.get(&n3.id).unwrap().clone());
        input_y3.insert(n2.id, y2.get(&n3.id).unwrap().clone());
        input_v3.insert(n1.id, v1.to_vec());
        input_v3.insert(n2.id, v2.to_vec());
        let mut input_y4: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v4: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y4.insert(n1.id, y1.get(&n4.id).unwrap().clone());
        input_y4.insert(n2.id, y2.get(&n4.id).unwrap().clone());
        input_v4.insert(n1.id, v1.to_vec());
        input_v4.insert(n2.id, v2.to_vec());
        let mut input_y5: HashMap<u128, Vec<u8>> = HashMap::new();
        let mut input_v5: HashMap<u128, Vec<k256::AffinePoint>> = HashMap::new();
        input_y5.insert(n1.id, y1.get(&n5.id).unwrap().clone());
        input_y5.insert(n2.id, y2.get(&n5.id).unwrap().clone());
        input_v5.insert(n1.id, v1.to_vec());
        input_v5.insert(n2.id, v2.to_vec());
        let (k2, K2, K_2) = &n2.resharing_round_2(&t_star, &new_quorum, input_y2, input_v2, K_dkg).unwrap();
        n2.private_share = *k2;
        n2.network_pubkey = *K_2;
        let (k3, K3, K_3) = &n3.resharing_round_2(&t_star, &new_quorum, input_y3, input_v3, K_dkg).unwrap();
        n3.private_share = *k3;
        n3.network_pubkey = *K_3;
        let (k4, K4, K_4) = &n4.resharing_round_2(&t_star, &new_quorum, input_y4, input_v4, K_dkg).unwrap();
        n4.private_share = *k4;
        n4.network_pubkey = *K_4;
        let (k5, K5, K_5) = &n5.resharing_round_2(&t_star, &new_quorum, input_y5, input_v5, K_dkg).unwrap();
        n5.private_share = *k5;
        n5.network_pubkey = *K_5;
        // We run resharing round 3 on new quorum composed of n2, n3 and n4
        let mut K_set = HashMap::new();
        K_set.insert(n2.id, K2.clone());
        K_set.insert(n3.id, K3.clone());
        K_set.insert(n4.id, K4.clone());
        K_set.insert(n5.id, K5.clone());
        let K_resharing = n2.resharing_round_3(&new_quorum, &K_set);
        let _ = n3.resharing_round_3(&new_quorum, &K_set);
        let _ = n4.resharing_round_3(&new_quorum, &K_set);
        let _ = n5.resharing_round_3(&new_quorum, &K_set);
    }
}
