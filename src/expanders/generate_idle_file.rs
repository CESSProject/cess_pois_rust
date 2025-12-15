//! # Hash Utilities Module
//!
//! This module provides a small abstraction layer over cryptographic
//! hash functions used throughout the system.
//!
//! It supports:
//! - SHA-256
//! - SHA-512
//!
//! The concrete hash algorithm is selected at compile time via
//! the [`HASH_SIZE`] constant, allowing consistent hash behavior
//! across the codebase.
//!
//! All hashing operations in this module are deterministic.

use sha2::{Digest, Sha256, Sha512};

/// Output size (in bytes) of the selected hash algorithm.
///
/// Supported values:
/// - `32` → SHA-256
/// - `64` → SHA-512
///
/// Any other value defaults to SHA-512.
pub const HASH_SIZE: i32 = 64;

/// Supported hash algorithm variants.
///
/// This enum wraps the underlying hasher implementation
/// and allows uniform handling of different hash functions.
pub enum Hasher {
    /// SHA-256 hash algorithm.
    SHA256(Sha256),

    /// SHA-512 hash algorithm.
    SHA512(Sha512),
}

/// Creates a new hasher instance based on [`HASH_SIZE`].
///
/// # Returns
/// A [`Hasher`] initialized with the selected hash algorithm.
pub fn new_hash() -> Hasher {
    match HASH_SIZE {
        32 => Hasher::SHA256(Sha256::new()),
        64 => Hasher::SHA512(Sha512::new()),
        _ => Hasher::SHA512(Sha512::new()),
    }
}

/// Computes the hash of the provided data.
///
/// If the input slice is empty, a fixed placeholder value (`"none"`)
/// is hashed instead to avoid hashing empty input.
///
/// # Parameters
/// - `data`: Input byte slice
///
/// # Returns
/// A byte vector containing the hash output.
pub fn get_hash(data: &[u8]) -> Vec<u8> {
    let hash = new_hash();
    let mut data = data;
    if data.is_empty() {
        data = b"none";
    }

    match hash {
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
    }
}
