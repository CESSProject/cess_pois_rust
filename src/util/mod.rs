//! # Utility Functions
//!
//! This module provides low-level helper utilities shared across
//! the verifier and prover implementations.
//!
//! It includes:
//! - Byte-slice composition helpers
//! - RSA accumulator key parsing
//! - In-place data combination utilities
//! - Memory clearing helpers
//!
//! These functions are intentionally minimal and optimized for
//! predictable, deterministic behavior.

use std::fs;

use crate::acc::{self, RsaKey};
use anyhow::Result;
use num_bigint_dig::BigUint;

/// Copies multiple byte slices into a target buffer sequentially.
///
/// Data from `src` is copied into `target` in order until the target
/// buffer is filled or input slices are exhausted.
///
/// Slices that would exceed the target buffer length are skipped.
///
/// # Parameters
/// - `target`: Destination buffer
/// - `src`: Source byte slices
pub fn copy_data(target: &mut [u8], src: &[&[u8]]) {
    let mut count = 0;
    let lens = target.len();

    for d in src {
        let l = d.len();
        if l == 0 || l + count > lens {
            continue;
        }
        target[count..count + l].copy_from_slice(d);
        count += l;
    }
}

/// Parses an RSA accumulator key from a file.
///
/// The file is expected to contain:
/// - 8 bytes: length of modulus `n`
/// - 8 bytes: length of generator `g`
/// - `n` bytes: modulus
/// - `g` bytes: generator
///
/// If parsing fails or the file is malformed, a new key is generated.
///
/// # Parameters
/// - `path`: Path to the key file
///
/// # Returns
/// A valid [`RsaKey`] instance.
pub fn parse_key(path: &str) -> Result<RsaKey> {
    let data = fs::read(path)?;
    Ok(get_key_from_bytes(&data))
}

/// Constructs an RSA accumulator key from raw bytes.
///
/// Falls back to generating a fresh key if the input format is invalid.
fn get_key_from_bytes(data: &[u8]) -> RsaKey {
    if data.len() < 8 {
        return acc::rsa_keygen(2048);
    }
    let nl = u64::from_be_bytes(data[..8].try_into().unwrap());
    let gl = u64::from_be_bytes(data[8..16].try_into().unwrap());
    if nl == 0 || gl == 0 || data.len() - 16 != (nl + gl) as usize {
        return acc::rsa_keygen(2048);
    }
    let n = BigUint::from_bytes_be(&data[16..16 + nl as usize]);
    let g = BigUint::from_bytes_be(&data[16 + nl as usize..]);
    RsaKey::new(n, g)
}

/// Combines multiple byte slices into a target buffer using XOR.
///
/// Each source slice must be at least as long as the target buffer.
/// Bytes are XORed positionally across all valid slices.
///
/// # Parameters
/// - `target`: Target buffer to modify in place
/// - `src`: Source byte slices
pub fn add_data(target: &mut [u8], src: &[&[u8]]) {
    let target_len = target.len();
    for s in src {
        if s.len() < target_len {
            continue;
        }
        for (i, elem) in target.iter_mut().enumerate() {
            *elem ^= s[i];
        }
    }
}

/// Clears a byte buffer by setting all elements to zero.
///
/// Useful for explicitly removing sensitive data from memory.
pub fn clear_data(target: &mut [u8]) {
    for element in target.iter_mut() {
        *element = 0;
    }
}
