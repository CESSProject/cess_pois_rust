//! # RSA Accumulator Construction Module
//!
//! This module provides utilities for constructing and updating
//! RSA-based cryptographic accumulators.
//!
//! It supports:
//! - RSA parameter generation
//! - Deterministic prime derivation from arbitrary data
//! - Accumulator updates over multiple elements
//!
//! The implementation is intended for cryptographic protocols that
//! require compact set commitments and membership proofs.


pub mod hash_2_prime;
pub mod multi_level_acc;

use num_bigint_dig::{BigUint, RandBigInt};
use num_integer::Integer;
use num_traits::One;
use rsa::{traits::PublicKeyParts, RsaPrivateKey};

use hash_2_prime::h_prime;

/// RSA accumulator public parameters.
///
/// The accumulator is defined over the multiplicative group `Z_n*`,
/// where `n` is an RSA modulus and `g` is a generator element.
///
/// These parameters are sufficient to compute accumulator values
/// but do not expose the RSA private key.
#[derive(Clone, Default, Debug)]
pub struct RsaKey {
    pub n: BigUint, //Z/nZ
    pub g: BigUint, // Generator
}
impl RsaKey {
    /// Constructs a new [`RsaKey`] from an existing modulus and generator.
    ///
    /// This function is intended for internal or controlled usage,
    /// where parameters are already validated.
    pub(crate) fn new(n: BigUint, g: BigUint) -> RsaKey {
        Self { n, g }
    }
}

/// Generates RSA accumulator parameters.
///
/// This function generates a fresh RSA modulus of size `lambda` bits
/// and derives a generator element that is coprime to the modulus.
///
/// # Parameters
/// - `lambda`: Bit length of the RSA modulus
///
/// # Returns
/// A fully initialized [`RsaKey`] suitable for accumulator operations.
pub fn rsa_keygen(lambda: usize) -> RsaKey {
    let mut rng = rand::thread_rng();
    let pk = RsaPrivateKey::new(&mut rng, lambda).expect("Failed to generate RSA key");

    let n = pk.n();
    let mut f: BigUint;

    // Select a random value coprime with n
    loop {
        f = rng.gen_biguint(lambda);
        if f.gcd(n) == BigUint::one() {
            break;
        }
    }

    // Square to ensure the generator lies in the quadratic residues
    let g = f.modpow(&BigUint::from(2u32), &n.clone());

    RsaKey { n: n.clone(), g }
}

/// Computes an RSA accumulator value over a set of elements.
///
/// The accumulator is updated by mapping each element to a
/// deterministic prime using `hash_2_prime`, and then exponentiating
/// the current accumulator value by that prime modulo `n`.
///
/// # Parameters
/// - `key`: RSA accumulator public parameters
/// - `acc`: Initial accumulator value (serialized)
/// - `elems`: Collection of elements to be accumulated
///
/// # Returns
/// - `Some(Vec<u8>)` containing the updated accumulator value
/// - `None` if the initial accumulator input is empty
pub fn generate_acc(key: &RsaKey, acc: &[u8], elems: Vec<Vec<u8>>) -> Option<Vec<u8>> {
    if acc.is_empty() {
        return None;
    }

    let mut g = BigUint::from_bytes_be(acc);
    for elem in elems {
        let prime = h_prime(&BigUint::from_bytes_be(&elem));
        g = g.modpow(&prime, &key.n);
    }

    Some(g.to_bytes_be())
}
