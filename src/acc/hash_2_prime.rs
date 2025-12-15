//! # Deterministic Prime Derivation Utilities
//!
//! This module provides utilities for deriving large prime numbers
//! deterministically from arbitrary big integers.
//!
//! It is designed for cryptographic and protocol-level use cases
//! where reproducible prime generation is required without relying
//! on randomness.
//!
//! Internally, the implementation combines:
//! - SHA-512 hashing
//! - Big integer arithmetic
//! - Logarithmic scaling
//! - Probabilistic primality testing
//!
//! All functions in this module are deterministic for a given input.

use std::{
    ops::{Div, Mul, Shl},
    str::FromStr,
};

use bigdecimal::BigDecimal;
use num_bigint_dig::{prime::probably_prime, BigUint};
use num_traits::{FromPrimitive, One, ToPrimitive};
use sha2::{Digest, Sha512};

/// Internal helper function used to derive a scaling factor from a big integer.
///
/// This function performs a series of arithmetic and logarithmic transformations
/// on the input value and produces a derived `BigUint` used as the base
/// for prime candidate generation.
///
/// The computation is deterministic and does not perform any primality checks.
///
/// # Parameters
/// - `x`: Input big integer
///
/// # Returns
/// A derived `BigUint` value used in prime candidate construction.
fn fu(x: &BigUint) -> BigUint {
    let u = x.clone();
    let one = BigUint::one();

    let two = BigUint::from(2u32);

    let mut temp1: BigUint = &u + &two;
    temp1 *= &two;
    let temp2 = &u + &one;
    let bit = temp2.bits();
    let divisor = one.shl(bit - 1);

    let f = BigDecimal::from_str(&temp2.to_string()).unwrap();
    let z = f.div(BigDecimal::from_str(divisor.to_string().as_str()).unwrap());
    let w = z.to_f64().unwrap();
    let y = (f64::log2(w) + (bit - 1) as f64).powi(2);
    let y = BigUint::from_f64(y).unwrap();
    let temp1 = &temp1.mul(&y);

    temp1.clone()
}

/// Derives a deterministic prime number from an input integer.
///
/// This function hashes the input using SHA-512, transforms the hash
/// into a numeric domain, and then iteratively searches for the first
/// prime number greater than or equal to the derived value.
///
/// Primality is verified using probabilistic testing with a fixed
/// number of rounds.
///
/// # Parameters
/// - `u`: Input big integer
///
/// # Returns
/// A prime `BigUint` deterministically derived from `u`.
pub fn h_prime(u: &BigUint) -> BigUint {
    let mut h = Sha512::new();
    h.update(u.to_bytes_be());
    let huj = fu(&BigUint::from_bytes_be(h.finalize().as_slice()));
    let mut j = huj.clone();
    let temp = huj;

    loop {
        let prime = &temp + &j;
        if probably_prime(&prime, 10) {
            return prime;
        }
        j += BigUint::from(1u32);
    }
}
