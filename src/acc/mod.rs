//! # RSA Accumulator Construction Module
//!
//! Provides:
//! - RSA parameter generation
//! - Deterministic prime derivation from arbitrary data
//! - Accumulator updates over single & multiple elements
//! - Single-element membership verification
//! - Recursive (parallel) witness generation
//!
//! Used by [`multi_level_acc`] and by the prover.

pub mod file_manage;
pub mod hash_2_prime;
pub mod multi_level_acc;

use num_bigint_dig::{BigUint, RandBigInt};
use num_integer::Integer;
use num_traits::One;
use rayon::join;
use rsa::{traits::PublicKeyParts, RsaPrivateKey};

use hash_2_prime::h_prime;

/// RSA accumulator public parameters.
#[derive(Clone, Default, Debug)]
pub struct RsaKey {
    pub n: BigUint, // Z/nZ
    pub g: BigUint, // Generator
}

impl RsaKey {
    /// Constructs a new [`RsaKey`] from an existing modulus and generator.
    pub fn new(n: BigUint, g: BigUint) -> RsaKey {
        Self { n, g }
    }
}

/// Generates fresh RSA accumulator parameters.
///
/// `lambda` is the modulus bit length (2048 is typical).
pub fn rsa_keygen(lambda: usize) -> RsaKey {
    let mut rng = rand::thread_rng();
    let pk = RsaPrivateKey::new(&mut rng, lambda).expect("Failed to generate RSA key");
    let n = pk.n();
    let mut f: BigUint;
    loop {
        f = rng.gen_biguint(lambda);
        if f.gcd(n) == BigUint::one() {
            break;
        }
    }
    let g = f.modpow(&BigUint::from(2u32), &n.clone());
    RsaKey { n: n.clone(), g }
}

/// Accumulates a fresh set of elements from raw initial accumulator value.
///
/// Equivalent to the Go-internal `generateAcc` helper.  Returns `None`
/// if `acc` is empty.
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

/// Builds an accumulator by exponentiating `G` with `H'(u)` for each `u`.
///
/// Mirrors the Go `GenerateAcc(key, U)`.
pub fn generate_acc_from_scratch(key: &RsaKey, us: &[Vec<u8>]) -> Vec<u8> {
    let mut g = key.g.clone();
    for u in us {
        let prime = h_prime(&BigUint::from_bytes_be(u));
        g = g.modpow(&prime, &key.n);
    }
    g.to_bytes_be()
}

/// Single-element accumulator membership check.
///
/// Equivalent to Go's `acc.Verify`.
pub fn verify(key: &RsaKey, acc: &[u8], u: &[u8], wit: &[u8]) -> bool {
    let e = h_prime(&BigUint::from_bytes_be(u));
    let dash = BigUint::from_bytes_be(wit).modpow(&e, &key.n);
    dash == BigUint::from_bytes_be(acc)
}

/// Generates a list of accumulator witnesses for `us`, parallel-recursively.
///
/// Mirrors Go's `GenerateWitness(G, N, us)`.
pub fn generate_witness(g: &BigUint, n: &BigUint, us: &[Vec<u8>]) -> Vec<Vec<u8>> {
    if us.is_empty() {
        return Vec::new();
    }
    if us.len() == 1 {
        return vec![g.to_bytes_be()];
    }
    let mid = us.len() / 2;
    let (left, right) = us.split_at(mid);

    // Compute g1 = g^{prod H'(u_i) for u in right}, g2 = g^{prod for left} in parallel.
    let g1 = compute_right_acc(g, n, right);
    let g2 = compute_right_acc(g, n, left);

    let (mut u1, mut u2) = join(
        || generate_witness(&g1, n, left),
        || generate_witness(&g2, n, right),
    );
    u1.append(&mut u2);
    u1
}

fn compute_right_acc(g: &BigUint, n: &BigUint, us: &[Vec<u8>]) -> BigUint {
    let mut acc = g.clone();
    for u in us {
        let e = h_prime(&BigUint::from_bytes_be(u));
        acc = acc.modpow(&e, n);
    }
    acc
}

/// Recursively populates the `wit` field of an `AccNode` slice with the
/// product-of-primes witnesses required for membership proofs.
pub fn gen_wits_for_acc_nodes(
    g: &BigUint,
    n: &BigUint,
    elems: &mut [multi_level_acc::AccNode],
) {
    let lens = elems.len();
    if lens == 0 {
        return;
    }
    if lens == 1 {
        elems[0].wit = g.to_bytes_be();
        return;
    }
    let mid = lens / 2;
    let (left, right) = elems.split_at_mut(mid);

    let right_vals: Vec<Vec<u8>> = right.iter().map(|n| n.value.clone()).collect();
    let left_vals: Vec<Vec<u8>> = left.iter().map(|n| n.value.clone()).collect();

    let (g1, g2) = join(
        || compute_right_acc(g, n, &right_vals),
        || compute_right_acc(g, n, &left_vals),
    );
    join(
        || gen_wits_for_acc_nodes(&g1, n, left),
        || gen_wits_for_acc_nodes(&g2, n, right),
    );
}
