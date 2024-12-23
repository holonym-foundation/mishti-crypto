use itertools::Itertools;
use num_bigint::BigUint;
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use tracing::info;
/// Allows a deterministic, uniform selection of t + epsilon nodes.
/// This way, each request should be mapped to a particular set of nodes.
/// Since it is uniform, this enables us to assume that all nodes should are
/// requested from equally. This simplifies accounting, so all nodes can be paid
/// equally assuming this mechanism works and they respond to all their requests.
/// n is the number of nodes, t is the threshold, and epsilon is the number of extra nodes to query
pub fn calc_nodes_to_send_to(epoch_num: u32, request_num: u128, t_plus_epsilon: u32, node_indices: Vec<usize>) -> Vec<u32> {
    let mut node_indices = node_indices.clone();
    let concatted: [u8; 32] = [(epoch_num as u128).to_be_bytes(), request_num.to_be_bytes()].concat().try_into().unwrap();
    info!(
        "Generating a 32-byte seed by concatenating the big-endian byte representations of epoch_num ({} as u128) and request_num ({}). \
        The resulting byte array is then converted into a fixed-size [u8; 32] array. Seed: {:02x?}  \
        node_indices :{:?}",
        epoch_num, request_num, concatted, node_indices
    );
    let mut rng = ChaCha8Rng::from_seed(concatted);
    let mut nodes_chosen = Vec::with_capacity(t_plus_epsilon as usize);
    for _i in 0..t_plus_epsilon {
        let num = rng.next_u64();
        info!("Rand Num :{} Nodes :{} ,Node chosen :{}", num, node_indices.len(), num % node_indices.len() as u64);
        let node_chosen_idx = num % node_indices.len() as u64;
        //    let node_chosen_idx = rng.next_u64() % (node_indices.len() as u64); // as long as there are not over 2^32 nodes, we don't have to worry about uniformity after modular reduction :) :)
        let node_chosen = node_indices.remove(node_chosen_idx as usize) as u32;
        // println!("Node chosen: {}", node_chosen);
        nodes_chosen.push(node_chosen);
    }
    nodes_chosen
}
/// A faster function to just calculate whether it should be sent to a particular node
pub fn should_be_sent_to_node(epoch_num: u32, request_num: u128, t_plus_epsilon: u32, node: u32, node_indexes: &[usize]) -> bool {
    let seed: [u8; 32] = [(epoch_num as u128).to_be_bytes(), request_num.to_be_bytes()].concat().try_into().unwrap();
    info!(
        "Generating a 32-byte seed by concatenating the big-endian byte representations of epoch_num ({} as u128) and request_num ({}). \
        The resulting byte array is then converted into a fixed-size [u8; 32] array. Seed: {:02x?}",
        epoch_num, request_num, seed
    );
    let mut rng = ChaCha8Rng::from_seed(seed);
    let mut node_indexes = node_indexes.to_vec();
    node_indexes.sort();

    for _ in 0..t_plus_epsilon {
        let num = rng.next_u64();
        info!("Rand Num :{} Nodes :{} ,Node chosen :{}", num, node_indexes.len(), num % node_indexes.len() as u64);
        let node_chosen_idx = num % node_indexes.len() as u64;
        let node_chosen_idx = node_indexes.remove(node_chosen_idx as usize);
        if node_chosen_idx == node as usize {
            return true;
        }
    }

    false
}
pub trait HasWeight {
    fn weight(&self) -> BigUint;
}
/// Chooses a node based on weight, such as stake
/// This could be more efficient but it's not a bottleneck. Alias method has O(1) time after O(n) preprocessing time if we want to optimize this by rewriting it
/// This method is easiest visualised:
/// Imagine all the weights are lines as long as their weights, merged into one line:
/// [ .................., ...., ..........., .........] (without the spaces and commas)
/// Then we choose a random number between 0 and the total weight, and find the first node that has a cumulative weight greater than or equal to the random number is chosen
/// [ .................., ...., ...*......., .........]
/// As you can see, the likelihood of a node being chosen is proportional to its weight
///
fn weighted_sample<T: HasWeight, R: Rng>(nodes: &[T], rng: &mut R) -> Option<usize> {
    // 1. Get the cumulative sum
    let cum_sum = nodes
        .iter()
        .scan(BigUint::ZERO, |acc, node| {
            *acc += node.weight();
            Some(acc.clone())
        })
        .collect_vec();
    // 2. Get total weight
    let total_weight = cum_sum.last()?.clone();
    // If the total weight is 0, we can't choose anything
    if total_weight == BigUint::ZERO {
        info!("Returning None since total weight is : {}", total_weight);
        return None;
    }
    // 3. Sample random number in [0, total_weight)
    let r = rng.gen_range(BigUint::ZERO..total_weight);
    // 4. Find the first node with cum_sum >= r
    let mut idx = None;
    for (i, _) in cum_sum.iter().enumerate().take(nodes.len()) {
        if cum_sum[i] >= r {
            idx = Some(i);
            break;
        }
    }
    idx
}
/// Samples n nodes with weights without replacement. n should be <= the number of nodes with non-zero weight
pub fn weighted_sample_n_no_replace<T: HasWeight + Clone>(nodes: Vec<T>, n: usize, random_seed: [u8; 32]) -> Option<Vec<T>> {
    let len = nodes.len();
    info!("Weighted Sampling [ (len == 0) || (n == 0) || (n > len)] {}", (len == 0) || (n == 0) || (n > len));
    if (len == 0) || (n == 0) || (n > len) {
        return None;
    }
    let mut r = ChaCha8Rng::from_seed(random_seed);
    let mut result = Vec::new();
    let mut the_nodes = nodes.clone();
    for _ in 0..n {
        let idx = weighted_sample(&the_nodes, &mut r)?;
        result.push(the_nodes.remove(idx));
    }
    Some(result)
}
#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::FromPrimitive;
    use rand::rngs::ThreadRng;
    #[test]
    fn test_calc_nodes_to_send_to() {
        let epoch_num = 123;
        let request_num = 321;
        let t_plus_epsilon = 2;
        let nodes = calc_nodes_to_send_to(epoch_num, request_num, t_plus_epsilon, vec![1, 2, 4]);
        assert_eq!(nodes.len(), t_plus_epsilon as usize);
        assert_eq!(nodes.iter().unique().count(), t_plus_epsilon as usize);
    }
    #[test]
    fn test_right_nodes_included() {
        let epoch_num = 123;
        let request_num = 321;
        let t_plus_epsilon = 2;
        let n = 3;
        let nodes = calc_nodes_to_send_to(epoch_num, request_num, t_plus_epsilon, vec![1, 2, 3]);
        println!("Nodes :{:?}", nodes);
        for node in nodes.clone() {
            assert!(should_be_sent_to_node(epoch_num, request_num, t_plus_epsilon, node, vec![1, 2, 3]));
        }
        let not_include = (1..n + 1).filter(|node| !nodes.contains(node));
        for node in not_include {
            assert!(!should_be_sent_to_node(epoch_num, request_num, t_plus_epsilon, node, vec![1, 2, 3]));
        }
    }
    /// For testing the stake-weighted sampling of nodes
    /// No need do derive these traits except for testing
    #[derive(Hash, Debug, Clone, Eq, PartialEq)]
    struct Node(u128);
    impl HasWeight for Node {
        fn weight(&self) -> BigUint { BigUint::from_u128(self.0).unwrap() }
    }
    #[test]
    fn test_weighted_distribution_length() {
        let nodes_0: Vec<Node> = vec![];
        let nodes_1_but_all_0 = vec![Node(0)];
        let nodes_1 = vec![Node(1)];
        let nodes_2 = vec![Node(0), Node(1)];
        let nodes_3 = vec![Node(0), Node(1), Node(2)];
        let nodes_4 = vec![Node(0), Node(1), Node(2), Node(3)];
        let mut rng: ThreadRng = ThreadRng::default();
        assert_eq!(weighted_sample_n_no_replace(nodes_0.clone(), 0, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_0.clone(), 1, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_1.clone(), 0, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_1_but_all_0, 1, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_1.clone(), 1, [0u8; 32]).unwrap().len(), 1);
        assert_eq!(weighted_sample_n_no_replace(nodes_2.clone(), 1, [0u8; 32]).unwrap().len(), 1);
        assert_eq!(weighted_sample_n_no_replace(nodes_2.clone(), 2, [0u8; 32]).unwrap().len(), 2);
        assert_eq!(weighted_sample_n_no_replace(nodes_2.clone(), 3, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_3.clone(), 4, [0u8; 32]), None);
        assert_eq!(weighted_sample_n_no_replace(nodes_4.clone(), 3, [0u8; 32]).unwrap().len(), 3);
        // This should returun None because it can't sample the 4th node of 0 weight:
        assert_eq!(weighted_sample_n_no_replace(nodes_4.clone(), 4, [0u8; 32]), None);
    }
    #[test]
    fn test_weighted_distribution() {
        let nodes = vec![Node(0), Node(1), Node(2), Node(3), Node(4), Node(5), Node(6), Node(7), Node(8), Node(9), Node(10)];
        let n = 4;
        let results = (0..1000).map(|_| weighted_sample(&nodes, &mut ThreadRng::default()).unwrap());
        let num_5_first = results.clone().filter(|r| *r == 5).count() as f64;
        let num_1_first = results.clone().filter(|r| *r == 1).count() as f64;
        println!("5s: {}, 1s: {}", num_5_first, num_1_first);
        // Check it's at the expected probability +- 1%
        assert!(num_1_first - 18.181818 < 10.0);
        assert!(num_5_first - 90.090909 < 10.0);
    }
    #[test]
    fn test_replacement() {
        // test the items are actually removed
        let nodes = vec![Node(0), Node(1), Node(2), Node(3), Node(4), Node(5), Node(6), Node(7), Node(8), Node(9), Node(10)];
        let n = 4;
        assert!((0..500)
            .map(|_| weighted_sample_n_no_replace(nodes.clone(), n, {
                let mut rnd = [0u8; 32];
                ThreadRng::default().fill_bytes(&mut rnd);
                rnd
            })
            .unwrap())
            .all(|r| r.iter().all_unique()));
    }
}
