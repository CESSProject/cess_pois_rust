//! # Stacked Expanders Construction Utilities
//!
//! This module provides helper functions for constructing and
//! initializing **stacked expander graphs**.
//!
//! It includes:
//! - Creation of expander graph configurations
//! - Deterministic parent selection for nodes
//!
//! These utilities are typically used in graph-based proof systems
//! and storage or computation verification protocols where
//! deterministic yet pseudo-random connectivity is required.

use sha2::{Digest, Sha512};

use super::{Expanders, Node, NodeType};

/// Constructs a stacked expander configuration.
///
/// This is a convenience wrapper around [`Expanders::new`].
///
/// # Parameters
/// - `k`: Number of stacked expander layers
/// - `n`: Number of nodes per layer
/// - `d`: Expansion degree (number of parents per node)
///
/// # Returns
/// An initialized [`Expanders`] configuration.
pub fn construct_stacked_expanders(k: i64, n: i64, d: i64) -> Expanders {
    Expanders::new(k, n, d)
}

/// Computes and assigns parent nodes for a given node.
///
/// Parent selection is deterministic and derived from:
/// - Miner identifier
/// - Layer index
/// - Node index
/// - Expansion parameters
///
/// Cryptographic hashing (SHA-512) is used to ensure
/// pseudo-random yet reproducible parent distribution.
///
/// # Parameters
/// - `expanders`: Expander graph configuration
/// - `node`: Node whose parents will be populated
/// - `miner_id`: Unique miner identifier
/// - `count`: Global counter value
/// - `rlayer`: Real layer index (used for layered expansion)
pub fn calc_parents(
    expanders: &Expanders,
    node: &mut Node,
    miner_id: &[u8],
    count: i64,
    rlayer: i64,
) {
    if node.parents.capacity() != (expanders.d + 1) as usize {
        return;
    }

    let layer = node.index as i64 / expanders.n;
    if layer == 0 {
        return;
    }

    let group_size = expanders.n / expanders.d;
    let offset = group_size / 256;

    let mut hash = Sha512::new();
    hash.update(miner_id);
    hash.update(count.to_be_bytes());
    hash.update(rlayer.to_be_bytes()); // add real layer
    hash.update((node.index as i64).to_be_bytes());
    let res = hash.clone().finalize();
    let mut res = res.to_vec();
    if expanders.d > 64 {
        hash.reset();
        hash.update(res.clone());
        let result = hash.finalize();
        res.append(&mut result.to_vec());
    }
    res = res[..expanders.d as usize].to_vec();

    let parent = node.index - expanders.n as NodeType;
    node.add_parent(parent);
    for i in 0..res.len() as i64 {
        let index = (layer - 1) * expanders.n
            + i * group_size
            + res[i as usize] as i64 * offset
            + res[i as usize] as i64 % offset;
        match index {
            i if i == parent as i64 => {
                node.add_parent((i + 1) as i32);
            }
            i if i < parent as i64 => {
                node.add_parent((i + expanders.n) as i32);
            }
            _ => {
                node.add_parent(index as i32);
            }
        }
    }
}
