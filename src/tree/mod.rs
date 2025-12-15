//! # Merkle Path Verification Utilities
//!
//! This module provides helper types and functions for verifying
//! **Merkle hash tree (MHT) inclusion proofs**.
//!
//! It supports:
//! - Verification of Merkle paths using SHA-based hashing
//! - Index-path consistency checks
//! - A lightweight hasher abstraction for SHA-256 and SHA-512
//!
//! These utilities are used throughout the verifier to validate
//! Merkle proofs embedded in commit, space, and deletion proofs.

use sha2::{Digest, Sha256, Sha512};

/// Merkle path proof.
///
/// Represents the data required to recompute a Merkle root
/// starting from a leaf value.
#[derive(Debug)]
pub struct PathProof {
    /// Location indicators for each level of the path.
    ///
    /// A value of `0` indicates the sibling hash is on the left,
    /// while `1` indicates it is on the right.
    pub locs: Vec<u8>,

    /// Sibling hash values along the path from leaf to root.
    pub path: Vec<Vec<u8>>,
}

/// Default hash output size (in bytes).
///
/// This value corresponds to SHA-256.
pub const DEFAULT_HASH_SIZE: u32 = 32;

/// Verifies a Merkle path proof.
///
/// Starting from the leaf `data`, this function iteratively hashes
/// sibling nodes according to `proof.locs` and compares the final
/// result against the expected Merkle `root`.
///
/// # Parameters
/// - `root`: Expected Merkle root hash
/// - `data`: Leaf data to verify
/// - `proof`: Merkle path proof
///
/// # Returns
/// `true` if the proof is valid, `false` otherwise.
pub fn verify_path_proof(root: &[u8], data: &[u8], proof: PathProof) -> bool {
    if proof.locs.len() != proof.path.len() {
        return false;
    }

    // Hash the leaf data first
    let hash = Hasher::SHA256(Sha256::new());
    let mut data = match hash {
        // TODO: write a generic function for the below task.
        Hasher::SHA256(hash) => {
            let mut hash = hash;
            hash.update(data);

            let result = hash.finalize();
            result.to_vec()
        }
        Hasher::SHA512(hash) => {
            let mut hash = hash;
            hash.update(data);

            let result = hash.finalize();
            result.to_vec()
        }
    };

    if data.len() != root.len() {
        return false;
    }
    for i in 0..proof.path.len() {
        let hash = Hasher::SHA256(Sha256::new());
        data = match hash {
            // TODO: write a generic function for the below task.
            Hasher::SHA256(hash) => {
                let mut hash = hash;

                if proof.locs[i] == 0 {
                    let mut proof_path_local = proof.path[i].to_owned();
                    proof_path_local.extend_from_slice(&data);
                    hash.update(proof_path_local);
                } else {
                    let mut proof_path_local = Vec::new();
                    proof_path_local.extend(data);
                    proof_path_local.extend(&proof.path[i]);
                    hash.update(proof_path_local);
                }
                let result = hash.finalize();
                result.to_vec()
            }
            Hasher::SHA512(hash) => {
                let mut hash = hash;
                if proof.locs[i] == 0 {
                    let mut proof_path_local = proof.path[i].to_owned();
                    proof_path_local.extend_from_slice(&data);
                    hash.update(proof_path_local);
                } else {
                    let mut proof_path_local = Vec::new();
                    proof_path_local.extend(data);
                    proof_path_local.extend(&proof.path[i]);
                    hash.update(proof_path_local);
                }
                let result = hash.finalize();
                result.to_vec()
            }
        };
    }
    root.eq(&data)
}

/// Checks whether a Merkle path location vector matches an index.
///
/// This function verifies that the left/right indicators in `locs`
/// are consistent with the binary representation of `index`.
///
/// # Parameters
/// - `index`: Leaf index in the Merkle tree
/// - `locs`: Location vector from the Merkle proof
///
/// # Returns
/// `true` if the index-path relationship is valid, `false` otherwise.
pub fn check_index_path(index: i64, locs: &[u8]) -> bool {
    let mut index = index;
    for v in locs {
        if (index + 1) % 2 == 0 {
            if *v != 0 {
                return false;
            }
        } else if *v != 1 {
            return false;
        }
        index /= 2;
    }
    true
}

/// Supported hash algorithm variants.
///
/// This enum wraps concrete hash implementations
/// used during Merkle proof verification.
pub enum Hasher {
    SHA256(Sha256),
    SHA512(Sha512),
}
