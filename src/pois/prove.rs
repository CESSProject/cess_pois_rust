//! # Proof and Commitment Data Structures
//!
//! This module defines the core data structures used to represent
//! **commitments and cryptographic proofs** across the system.
//!
//! It includes:
//! - Commit metadata
//! - Merkle hash tree (MHT) proofs
//! - RSA accumulator witness chains
//! - Space and deletion proofs
//!
//! These structures are primarily used as serialized payloads
//! exchanged between prover and verifier components.

use serde::{Deserialize, Serialize};

use crate::{acc::multi_level_acc::WitnessNode, expanders::NodeType};

/// Commit metadata associated with stored files.
///
/// A commit links file indices to their corresponding Merkle roots.
#[derive(Clone, Default, Debug, PartialEq, Serialize, Deserialize)]
pub struct Commits {
    /// Indices of committed files.
    pub file_indexs: Vec<i64>,

    /// Merkle root hashes corresponding to each file.
    pub roots: Vec<Vec<u8>>,
}

/// Merkle Hash Tree (MHT) proof node.
///
/// Represents a membership proof for a single leaf or internal node
/// in a Merkle tree.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct MhtProof {
    /// Index of the node within the tree.
    pub index: NodeType,

    /// Hash label of the node.
    pub label: Vec<u8>,

    /// Sibling hash path from the node to the root.
    pub paths: Vec<Vec<u8>>,

    /// Bitfield indicating left/right sibling positions.
    pub locs: Vec<u8>,
}

/// Commitment proof structure.
///
/// Contains Merkle proofs for a node, its parents,
/// and higher-level ancestor nodes.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct CommitProof {
    /// Merkle proof for the target node.
    pub node: MhtProof,

    /// Merkle proofs for parent nodes.
    pub parents: Vec<MhtProof>,

    /// Merkle proofs for elder (higher-level) nodes.
    pub elders: Vec<MhtProof>,
}

/// RSA accumulator proof.
///
/// Represents membership proofs within an RSA accumulator,
/// including witness chains and accumulator paths.
#[derive(Debug, Default)]
pub struct AccProof {
    /// Indices associated with accumulator elements.
    pub indexs: Vec<i64>,
    /// Labels corresponding to accumulator elements.
    pub labels: Vec<Vec<u8>>,
    /// Optional multi-level witness chain.
    pub wit_chains: Option<Box<WitnessNode>>,
    /// Accumulator path values from leaf to root.
    pub acc_path: Vec<Vec<u8>>,
}

/// Proof of storage space.
///
/// Combines Merkle proofs and accumulator witnesses to
/// demonstrate valid storage over a specific range.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct SpaceProof {
    /// Left boundary of the proven range.
    pub left: i64,
    /// Right boundary of the proven range.
    pub right: i64,
    /// Merkle proofs for challenged segments.
    pub proofs: Vec<Vec<MhtProof>>,
    /// Merkle roots associated with the proof.
    pub roots: Vec<Vec<u8>>,
    /// RSA accumulator witness chains.
    pub wit_chains: Vec<WitnessNode>,
}

/// Proof of deletion.
///
/// Demonstrates that data has been removed correctly
/// from both Merkle structures and accumulators.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct DeletionProof {
    pub roots: Vec<Vec<u8>>,
    pub wit_chain: WitnessNode,
    pub acc_path: Vec<Vec<u8>>,
}
