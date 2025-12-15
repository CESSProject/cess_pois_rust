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
use std::mem;

use num_bigint_dig::BigInt;
use num_traits::{Signed, ToPrimitive};

/// Re-exported hash constructor used by expander generation.
pub use generate_idle_file::new_hash;

/// Node index type used throughout the expander graph.
pub type NodeType = i32;

/// Stacked expander graph configuration.
///
/// Defines the structural parameters required to construct
/// a multi-layer expander graph.
#[derive(Clone, Debug)]
pub struct Expanders {
    /// Number of expander layers.
    pub k: i64,

    /// Number of nodes per layer.
    pub n: i64,

    /// Expansion degree (number of parents per node).
    pub d: i64,

    /// Total number of nodes in the stacked expander.
    pub size: i64,

    /// Hash output size (in bytes).
    pub hash_size: i64,
}

/// Node in an expander graph.
///
/// Each node maintains an ordered list of parent node indices.
pub struct Node {
    /// Index of the node in the stacked graph.
    pub index: NodeType,

    /// Sorted list of parent node indices.
    pub parents: Vec<NodeType>,
}

impl Expanders {
    /// Creates a new stacked expander configuration.
    ///
    /// # Parameters
    /// - `k`: Number of expander layers
    /// - `n`: Number of nodes per layer
    /// - `d`: Expansion degree
    pub fn new(k: i64, n: i64, d: i64) -> Self {
        Expanders {
            k,
            n,
            d,
            size: (k + 1) * n,
            hash_size: 64,
        }
    }
}

impl Node {
    /// Creates a new node with the given index.
    pub fn new(idx: NodeType) -> Self {
        Self {
            index: idx,
            parents: Vec::new(),
        }
    }

    /// Inserts a parent node index into the parent list.
    ///
    /// The parent list is kept sorted and free of duplicates.
    ///
    /// # Returns
    /// `true` if the parent was inserted, `false` otherwise.
    pub fn add_parent(&mut self, parent: NodeType) -> bool {
        if self.index == parent {
            return false;
        }
        if self.parents.is_empty() || self.parents.len() >= self.parents.capacity() {
            return false;
        }

        let (i, ok) = self.parent_in_list(parent);
        if ok {
            return false;
        }
        self.parents.push(0);
        let lens = self.parents.len();
        if lens == 1 || i == lens as i32 - 1 {
            self.parents[i as usize] = parent;
            return true;
        }
        self.parents
            .copy_within(i as usize + 1..lens - 1, i as usize);
        self.parents[i as usize] = parent;

        true
    }

    /// Checks whether the node has no parents.
    pub fn no_parents(&self) -> bool {
        self.parents.is_empty()
    }

    /// Determines whether a parent exists in the list.
    ///
    /// Returns the insertion index and a boolean indicating presence.
    pub fn parent_in_list(&self, parent: NodeType) -> (i32, bool) {
        if self.no_parents() {
            return (0, false);
        }
        let lens = self.parents.len();
        let (mut l, mut r) = (0, lens - 1);
        while l <= r {
            let mid = (l + r) / 2;
            if self.parents[mid] == parent {
                return (0, true);
            }
            if self.parents[mid] > parent {
                r = mid - 1;
            } else {
                l = mid + 1;
            }
        }
        let mut i = (l + r) / 2;
        if self.parents[i] < parent {
            i += 1;
        }
        (i as i32, false)
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

/// Maps arbitrary bytes to a valid node index.
///
/// The result is guaranteed to lie in the range `[0, max)`.
pub fn bytes_to_node_value(data: &[u8], max: i64) -> NodeType {
    let value = BigInt::from_bytes_be(num_bigint_dig::Sign::Plus, data);
    let big_max = BigInt::from(max);

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
