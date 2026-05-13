//! # Algorithmic Go-↔-Rust compatibility tests
//!
//! Pin down behaviour for hashing, byte encoding, prime derivation, and
//! Merkle tree construction so a faulty refactor immediately surfaces.

use cess_pois_rust::acc::hash_2_prime::h_prime;
use cess_pois_rust::acc::{generate_acc, rsa_keygen};
use cess_pois_rust::expanders::{
    bytes_to_int64, get_bytes, get_bytes_slice, NodeType,
};
use cess_pois_rust::tree::{
    calc_light_mht_with_bytes, get_path_proof, get_root, verify_path_proof, DEFAULT_HASH_SIZE,
};
use num_bigint_dig::BigUint;
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// 1. `get_bytes` and `get_bytes_slice` — must be big-endian.
// ---------------------------------------------------------------------------

#[test]
fn get_bytes_is_big_endian_for_i64_i32_u32() {
    // i64 -> 8 bytes BE
    assert_eq!(
        get_bytes(0x0123456789abcdef_i64),
        vec![0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
    );
    // NodeType (i32) -> 4 bytes BE
    let x: NodeType = 0x01020304;
    assert_eq!(get_bytes(x), vec![0x01, 0x02, 0x03, 0x04]);
    // u32 -> 4 bytes BE
    assert_eq!(get_bytes(0xaabbccdd_u32), vec![0xaa, 0xbb, 0xcc, 0xdd]);
}

#[test]
fn get_bytes_slice_concatenates_big_endian() {
    let v: Vec<i64> = vec![1, 2, 3];
    assert_eq!(
        get_bytes_slice(&v),
        vec![
            0, 0, 0, 0, 0, 0, 0, 1, // 1
            0, 0, 0, 0, 0, 0, 0, 2, // 2
            0, 0, 0, 0, 0, 0, 0, 3, // 3
        ]
    );
}

#[test]
fn bytes_to_int64_matches_go_big_endian_mod() {
    // big.Int{} from bytes {1,2}, mod 100 = 258 % 100 = 58
    assert_eq!(bytes_to_int64(&[1, 2], 100), 58);
    // 0xFF = 255 mod 100 = 55
    assert_eq!(bytes_to_int64(&[0xff], 100), 55);
    // Large hash, max=15: result must be in [0, 15)
    let hash = [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe];
    let v = bytes_to_int64(&hash, 15);
    assert!((0..15).contains(&v), "value out of range: {}", v);
}

// ---------------------------------------------------------------------------
// 2. `h_prime` is deterministic and produces an odd prime.
// ---------------------------------------------------------------------------

#[test]
fn h_prime_is_deterministic_and_odd() {
    let x = BigUint::from(42u32);
    let a = h_prime(&x);
    let b = h_prime(&x);
    assert_eq!(a, b, "h_prime must be deterministic");
    // Primes (other than 2) are odd; h_prime emits 256-bit candidates so it
    // should always be odd here.
    assert!(&a % 2u32 != BigUint::from(0u32), "h_prime returned even");
}

// ---------------------------------------------------------------------------
// 3. RSA accumulator math: `g^p1^p2 == (g^p1)^p2`.
// ---------------------------------------------------------------------------

#[test]
fn accumulator_exponent_is_associative() {
    let key = rsa_keygen(512);
    let g_bytes = key.g.to_bytes_be();
    let a = vec![1u8, 2, 3];
    let b = vec![4u8, 5, 6];

    let acc_ab = generate_acc(&key, &g_bytes, vec![a.clone(), b.clone()]).unwrap();
    let acc_a = generate_acc(&key, &g_bytes, vec![a]).unwrap();
    let acc_ab2 = generate_acc(&key, &acc_a, vec![b]).unwrap();

    assert_eq!(acc_ab, acc_ab2);
}

// ---------------------------------------------------------------------------
// 4. LightMHT layout for n=4 — root is mht[32..64], hashes match SHA-256.
// ---------------------------------------------------------------------------

#[test]
fn light_mht_root_matches_recursive_sha256_for_n_4() {
    let size = 16;
    let leaves: [[u8; 16]; 4] = [
        *b"aaaaaaaaaaaaaaaa",
        *b"bbbbbbbbbbbbbbbb",
        *b"cccccccccccccccc",
        *b"dddddddddddddddd",
    ];
    let mut flat = Vec::with_capacity(4 * size);
    for leaf in &leaves {
        flat.extend_from_slice(leaf);
    }
    let mut mht = vec![0u8; 4 * DEFAULT_HASH_SIZE];
    calc_light_mht_with_bytes(&mut mht, &flat, size);

    // Compute expected root by hand: H(H(H(a)||H(b)) || H(H(c)||H(d))).
    let h = |x: &[u8]| -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(x);
        h.finalize().to_vec()
    };
    let h_concat = |x: &[u8], y: &[u8]| -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(x);
        h.update(y);
        h.finalize().to_vec()
    };

    let ha = h(&leaves[0]);
    let hb = h(&leaves[1]);
    let hc = h(&leaves[2]);
    let hd = h(&leaves[3]);
    let hab = h_concat(&ha, &hb);
    let hcd = h_concat(&hc, &hd);
    let root_expected = h_concat(&hab, &hcd);

    let root_got = get_root(&mht);
    assert_eq!(root_got, root_expected);
}

// ---------------------------------------------------------------------------
// 5. Round-trip a path proof (leaf -> root) using the public verifier.
// ---------------------------------------------------------------------------

#[test]
fn light_mht_path_proof_roundtrip() {
    let size = 16;
    let n = 8usize;
    let mut flat = Vec::with_capacity(n * size);
    for i in 0..n {
        let leaf = vec![i as u8; size];
        flat.extend_from_slice(&leaf);
    }
    let mut mht = vec![0u8; n * DEFAULT_HASH_SIZE];
    calc_light_mht_with_bytes(&mut mht, &flat, size);
    let root = get_root(&mht);

    for index in 0..n {
        let leaf = &flat[index * size..(index + 1) * size];
        let proof = get_path_proof(&mht, &flat, index, size).expect("proof");
        assert!(
            verify_path_proof(&root, leaf, proof),
            "path proof failed at index {}",
            index
        );
    }
}

// ---------------------------------------------------------------------------
// 6. LightMHT does not panic for larger n where the algorithm naturally
//    stops before reaching size=32 at the very top (this used to panic).
// ---------------------------------------------------------------------------

#[test]
fn light_mht_large_n_does_not_panic() {
    // Pick n=64 leaves of 32 bytes each. With the old code the top
    // iteration had pair_count=0 and tried to copy_from_slice(0) into a
    // non-empty target — now fixed.
    let n = 64usize;
    let size = DEFAULT_HASH_SIZE;
    let flat = vec![0xaa_u8; n * size];
    let mut mht = vec![0u8; n * size];
    calc_light_mht_with_bytes(&mut mht, &flat, size);
    let _root = get_root(&mht);
}
