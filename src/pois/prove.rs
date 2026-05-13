//! # Proof and Commitment Data Structures
//!
//! Defines the data structures exchanged between prover and verifier.
//!
//! **JSON wire format**: every `Vec<u8>` / `Vec<Vec<u8>>` field below uses
//! the Go-compatible base64 string encoding (see
//! [`crate::util::json_bytes`]).  This guarantees Go-written payloads
//! parse cleanly in Rust and vice versa.

use serde::{Deserialize, Serialize};

use crate::{acc::multi_level_acc::WitnessNode, expanders::NodeType};

/// Commit metadata associated with stored files.
///
/// A commit links file indices to their corresponding Merkle roots.
#[derive(Clone, Default, Debug, PartialEq, Serialize, Deserialize)]
pub struct Commits {
    /// Indices of committed files.
    #[serde(default)]
    pub file_indexs: Vec<i64>,

    /// Merkle root hashes corresponding to each file.
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub roots: Vec<Vec<u8>>,
}

/// Merkle Hash Tree (MHT) proof node.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct MhtProof {
    /// Index of the node within the tree.
    #[serde(default)]
    pub index: NodeType,

    /// Hash label of the node.
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub label: Vec<u8>,

    /// Sibling hash path from the node to the root.
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub paths: Vec<Vec<u8>>,

    /// Bitfield indicating left/right sibling positions.
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub locs: Vec<u8>,
}

/// Commitment proof structure.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct CommitProof {
    /// Merkle proof for the target node.
    pub node: MhtProof,

    /// Merkle proofs for parent nodes.
    #[serde(default)]
    pub parents: Vec<MhtProof>,

    /// Merkle proofs for elder (higher-level) nodes.
    #[serde(default)]
    pub elders: Vec<MhtProof>,
}

/// RSA accumulator proof.
#[derive(Debug, Default, Deserialize, Serialize)]
pub struct AccProof {
    /// Indices associated with accumulator elements.
    #[serde(default)]
    pub indexs: Vec<i64>,
    /// Labels corresponding to accumulator elements.
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub labels: Vec<Vec<u8>>,
    /// Optional multi-level witness chain.
    #[serde(default)]
    pub wit_chains: Option<Box<WitnessNode>>,
    /// Accumulator path values from leaf to root.
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub acc_path: Vec<Vec<u8>>,
}

/// Proof of storage space.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct SpaceProof {
    /// Left boundary of the proven range.
    pub left: i64,
    /// Right boundary of the proven range.
    pub right: i64,
    /// Merkle proofs for challenged segments.
    #[serde(default)]
    pub proofs: Vec<Vec<MhtProof>>,
    /// Merkle roots associated with the proof.
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub roots: Vec<Vec<u8>>,
    /// RSA accumulator witness chains.
    #[serde(default)]
    pub wit_chains: Vec<WitnessNode>,
}

/// Proof of deletion.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct DeletionProof {
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub roots: Vec<Vec<u8>>,
    #[serde(default)]
    pub wit_chain: WitnessNode,
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub acc_path: Vec<Vec<u8>>,
}
