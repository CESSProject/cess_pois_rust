//! # Expander Graph Core Structures and Utilities
//!
//! This module defines the core data structures and helper utilities
//! used to construct and manipulate **stacked expander graphs**.
//!
//! It provides:
//! - Expander configuration parameters
//! - Node representation and parent management
//! - Byte-encoding helpers for deterministic hashing
//! - Utilities for mapping hash output into node indices
//!
//! These components are foundational for graph-based proof systems
//! and deterministic graph construction protocols.

pub mod generate_expanders;
pub mod generate_idle_file;

use std::fs;
use std::mem;

use anyhow::{Context, Result};
use num_bigint_dig::BigInt;
use num_traits::{Signed, ToPrimitive};
use serde::{Deserialize, Serialize};

/// Re-exported hash constructor used by expander generation.
pub use generate_idle_file::{new_hash, HASH_SIZE};

/// Node index type used throughout the expander graph.
pub type NodeType = i32;

/// Maximum allowed expansion degree.
pub const MAX_DEGREE: i64 = 128;

/// Stacked expander graph configuration.
///
/// Defines the structural parameters required to construct
/// a multi-layer expander graph.
///
/// JSON layout matches Go's `expanders.Expanders` (Go marshals untagged
/// fields with their Go field name, hence `K`, `N`, `D` are capitalised).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Expanders {
    /// Number of expander layers.
    #[serde(rename = "K")]
    pub k: i64,

    /// Number of nodes per layer.
    #[serde(rename = "N")]
    pub n: i64,

    /// Expansion degree (number of parents per node).
    #[serde(rename = "D")]
    pub d: i64,

    /// Total number of nodes in the stacked expander.
    pub size: i64,

    /// Hash output size (in bytes).
    #[serde(rename = "hash_szie")] // matches the (typo'd) Go JSON tag for interop
    pub hash_size: i64,
}

/// Node in an expander graph.
///
/// Each node maintains an ordered list of parent node indices.
#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct Node {
    /// Index of the node in the stacked graph.
    pub index: NodeType,

    /// Sorted list of parent node indices.
    pub parents: Vec<NodeType>,
}

impl Expanders {
    /// Creates a new stacked expander configuration.
    pub fn new(k: i64, n: i64, d: i64) -> Self {
        let d = if d > MAX_DEGREE { MAX_DEGREE } else { d };
        Expanders {
            k,
            n,
            d,
            size: (k + 1) * n,
            hash_size: HASH_SIZE as i64,
        }
    }

    /// Serializes the expander config as JSON and writes it to disk.
    pub fn marshal_and_save<P: AsRef<std::path::Path>>(&self, path: P) -> Result<()> {
        let data = serde_json::to_vec(self).with_context(|| "marshal expanders error")?;
        crate::util::save_file(&path, &data).with_context(|| "save expanders error")
    }
}

/// Loads an expander configuration from disk.
pub fn read_and_unmarshal_expanders<P: AsRef<std::path::Path>>(path: P) -> Result<Expanders> {
    let data = fs::read(&path).with_context(|| "read expanders error")?;
    let exp: Expanders =
        serde_json::from_slice(&data).with_context(|| "unmarshal expanders error")?;
    Ok(exp)
}

impl Node {
    /// Creates a new node with the given index. The parents vector is
    /// allocated empty — callers that intend to compute parents should
    /// pre-allocate via [`Node::with_capacity`].
    pub fn new(idx: NodeType) -> Self {
        Self {
            index: idx,
            parents: Vec::new(),
        }
    }

    /// Creates a node with the parents vector pre-sized for `d + 1` entries.
    pub fn with_capacity(idx: NodeType, d: i64) -> Self {
        Self {
            index: idx,
            parents: Vec::with_capacity((d + 1) as usize),
        }
    }

    /// Inserts a parent node index into the parent list.
    ///
    /// The parent list is kept sorted and free of duplicates.
    ///
    /// Returns `true` if the parent was inserted.
    pub fn add_parent(&mut self, parent: NodeType) -> bool {
        if self.index == parent {
            return false;
        }
        if self.parents.capacity() == 0 || self.parents.len() >= self.parents.capacity() {
            return false;
        }

        let (i, ok) = self.parent_in_list(parent);
        if ok {
            return false;
        }
        self.parents.insert(i as usize, parent);
        true
    }

    /// Checks whether the node has no parents.
    pub fn no_parents(&self) -> bool {
        self.parents.is_empty()
    }

    /// Binary search for `parent`. Returns `(insertion_index, present)`.
    pub fn parent_in_list(&self, parent: NodeType) -> (i32, bool) {
        if self.no_parents() {
            return (0, false);
        }
        let lens = self.parents.len() as i32;
        let (mut l, mut r) = (0i32, lens - 1);
        while l <= r {
            let mid = (l + r) / 2;
            if self.parents[mid as usize] == parent {
                return (0, true);
            }
            if self.parents[mid as usize] > parent {
                r = mid - 1;
            } else {
                l = mid + 1;
            }
        }
        let mut i = (l + r) / 2;
        if i < 0 {
            i = 0;
        }
        if (i as usize) < self.parents.len() && self.parents[i as usize] < parent {
            i += 1;
        }
        (i, false)
    }
}

/// Serializes a numeric value into big-endian bytes.
///
/// The byte length is derived from the size of `T`.
pub fn get_bytes<T: ToPrimitive>(v: T) -> Vec<u8> {
    let size = mem::size_of::<T>();
    let value = v.to_i64().unwrap();
    let mut bytes = vec![0; size];
    for i in 0..size {
        bytes[size - 1 - i] = ((value >> (8 * i)) & 0xFF) as u8;
    }
    bytes
}

/// Serializes a slice of numeric values into big-endian bytes.
pub fn get_bytes_slice<T: ToPrimitive>(values: &[T]) -> Vec<u8> {
    let size = mem::size_of::<T>();
    let mut bytes = Vec::with_capacity(size * values.len());
    for v in values {
        let value = v.to_i64().unwrap();
        for i in 0..size {
            bytes.push(((value >> (8 * (size - 1 - i))) & 0xFF) as u8);
        }
    }
    bytes
}

/// Maps arbitrary bytes to a valid node index in `[0, max)`.
///
/// **Note**: Go's `BytesToNodeValue` uses `binary.Varint` (zig-zag decoding
/// of the first ~9 bytes).  This Rust implementation uses big-endian
/// reduce-mod instead — semantically different.  In the Go reference
/// `BytesToNodeValue` is *dead code* (it has no callers), so the
/// divergence does not affect on-the-wire compatibility.  Use
/// [`bytes_to_int64`] for the formula Go actually uses in
/// `NewChallengeHandle`.
pub fn bytes_to_node_value(data: &[u8], max: i64) -> NodeType {
    let value = BigInt::from_bytes_be(num_bigint_dig::Sign::Plus, data);
    let big_max = BigInt::from(max.max(1));
    let value = value % &big_max;
    let i_value = value.to_i64().unwrap_or_else(|| {
        if value.is_negative() {
            i64::MIN
        } else {
            i64::MAX
        }
    });
    ((i_value + max) % max) as NodeType
}

/// Maps arbitrary bytes to an `i64` in `[0, max)` via big-endian integer reduction.
///
/// Equivalent to Go's `BytesToInt64`.
pub fn bytes_to_int64(data: &[u8], max: i64) -> i64 {
    let value = num_bigint_dig::BigUint::from_bytes_be(data);
    let big_max = num_bigint_dig::BigUint::from(max as u64);
    let v = value % big_max;
    let iv: i64 = v.to_i64().unwrap_or(0).abs();
    iv % max
}
