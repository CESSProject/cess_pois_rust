//! # Light-Weight Merkle Hash Tree (LightMHT)
//!
//! A flat-array Merkle tree used to commit to fixed-size leaves.
//! The layout matches the Go reference (`tree/light_merkel_tree.go`):
//!
//! ```text
//! [ leaf_hashes (n) | level_1 (n/2) | level_2 (n/4) | ... | root_pair ]
//! ```
//!
//! All node hashes are SHA-256 and each occupies [`DEFAULT_HASH_SIZE`] bytes.
//!
//! In addition to construction, this module provides path-proof
//! generation (with and without an `aux` mid-tree cache) and the
//! verifier-side path proof checking already required by `pois`.

use lazy_static::lazy_static;
use parking_lot::Mutex;
use sha2::{Digest, Sha256};

/// SHA-256 output size, in bytes.
pub const DEFAULT_HASH_SIZE: usize = 32;

/// Flat-array Merkle tree backing store.
///
/// Equivalent to Go's `LightMHT = []byte`.
pub type LightMHT = Vec<u8>;

/// Merkle path proof.
#[derive(Clone, Debug, Default)]
pub struct PathProof {
    /// `0` means sibling is on the left, `1` means sibling is on the right.
    pub locs: Vec<u8>,
    /// Sibling hashes from leaf to root.
    pub path: Vec<Vec<u8>>,
}

// -----------------------------------------------------------------------------
// Pool — replaces Go's `sync.Pool` for reusable tree backing buffers.
// -----------------------------------------------------------------------------

struct MhtPool {
    elem_len: usize,
    free: Vec<LightMHT>,
}

lazy_static! {
    static ref MHT_POOL: Mutex<Option<MhtPool>> = Mutex::new(None);
}

/// Initialises the global Merkle-tree backing-buffer pool.
///
/// `e_len` is the number of leaves a single buffer needs to support
/// (matches the Go `InitMhtPool(eLen int)` semantics).
pub fn init_mht_pool(e_len: usize) {
    let mut guard = MHT_POOL.lock();
    if guard.is_some() {
        return;
    }
    *guard = Some(MhtPool {
        elem_len: e_len * DEFAULT_HASH_SIZE,
        free: Vec::new(),
    });
}

/// Obtains a Merkle-tree backing buffer from the pool.
///
/// The buffer is zero-filled.  If the pool has not been initialised this
/// falls back to a one-off allocation of [`DEFAULT_HASH_SIZE`] bytes
/// so callers that bypass [`init_mht_pool`] still get something useful.
pub fn get_light_mht_from_pool() -> LightMHT {
    let mut guard = MHT_POOL.lock();
    if let Some(pool) = guard.as_mut() {
        if let Some(mut buf) = pool.free.pop() {
            for b in buf.iter_mut() {
                *b = 0;
            }
            return buf;
        }
        return vec![0u8; pool.elem_len];
    }
    vec![0u8; DEFAULT_HASH_SIZE]
}

/// Returns a Merkle-tree backing buffer to the pool.
pub fn put_light_mht_to_pool(mht: LightMHT) {
    let mut guard = MHT_POOL.lock();
    if let Some(pool) = guard.as_mut() {
        if mht.len() == pool.elem_len {
            pool.free.push(mht);
        }
    }
}

// -----------------------------------------------------------------------------
// Construction
// -----------------------------------------------------------------------------

/// Builds the Merkle tree from `data`, where `data` is a flat concatenation
/// of fixed-size leaves of length `size`.
pub fn calc_light_mht_with_bytes(mht: &mut LightMHT, data: &[u8], size: usize) {
    let leaves = data.len() / size;
    let mut hasher = Sha256::new();
    for i in 0..leaves {
        hasher.update(&data[i * size..(i + 1) * size]);
        let result = hasher.finalize_reset();
        mht[i * DEFAULT_HASH_SIZE..(i + 1) * DEFAULT_HASH_SIZE].copy_from_slice(&result);
    }
    calc_light_mht(mht);
}

/// Initialises the tree directly from a pre-computed aux slice (which
/// already contains hashed leaves) and finishes the upper levels.
pub fn calc_light_mht_with_aux(mht: &mut LightMHT, aux: &[u8]) {
    let n = aux.len().min(mht.len());
    mht[..n].copy_from_slice(&aux[..n]);
    calc_light_mht(mht);
}

/// Internal helper that fills in the non-leaf levels of the tree.
///
/// Implementation mirrors the in-place layout of the Go reference:
/// each level is half the previous one and written into the same
/// backing buffer.
fn calc_light_mht(mht: &mut LightMHT) {
    let lens = mht.len();
    let size = DEFAULT_HASH_SIZE;
    if lens < 2 * size {
        return;
    }
    let levels = ((lens / size) as f64).log2() as usize + 1;

    let mut hasher = Sha256::new();
    let mut p = lens / 2;
    let mut src_start = 0usize;

    for i in 0..levels {
        let num = lens / (1usize << (i + 1));
        let pair_count = num / size;
        // Matches Go's behaviour: when num shrinks below `size`, the inner
        // loop is a no-op and nothing is written to the target slot.
        // (Happens at the very top of the tree for any n ≥ 64.)
        if pair_count == 0 {
            let target_start = p;
            src_start = target_start;
            p /= 2;
            continue;
        }
        let target_start = p;
        // We have to read from `src` (mht[src_start..]) before writing to
        // `target` (mht[p..p+num]); since these ranges can overlap, we
        // pre-stage the hashes into a small local buffer.
        let mut new_level = Vec::with_capacity(pair_count * size);
        for j in 0..pair_count {
            let k = j * 2;
            let lo = src_start + k * size;
            let hi = lo + 2 * size;
            hasher.update(&mht[lo..hi]);
            new_level.extend_from_slice(&hasher.finalize_reset());
        }
        mht[target_start..target_start + new_level.len()].copy_from_slice(&new_level);
        src_start = target_start;
        p /= 2;
    }
}

/// Returns the Merkle root, or an empty slice if the tree is too small.
pub fn get_root(mht: &LightMHT) -> Vec<u8> {
    if mht.len() < DEFAULT_HASH_SIZE * 2 {
        return Vec::new();
    }
    mht[DEFAULT_HASH_SIZE..DEFAULT_HASH_SIZE * 2].to_vec()
}

// -----------------------------------------------------------------------------
// Path proofs
// -----------------------------------------------------------------------------

/// Generates a path proof for the leaf at `index`.
pub fn get_path_proof(
    mht: &LightMHT,
    data: &[u8],
    index: usize,
    size: usize,
) -> anyhow::Result<PathProof> {
    get_path_proof_inner(mht, data, index, size, false)
}

fn get_path_proof_inner(
    mht: &LightMHT,
    data: &[u8],
    mut index: usize,
    mut size: usize,
    hashed: bool,
) -> anyhow::Result<PathProof> {
    let deep = ((data.len() / size) as f64).log2() as usize;
    let mut proof = PathProof {
        locs: vec![0u8; deep],
        path: Vec::with_capacity(deep),
    };
    for _ in 0..deep {
        proof.path.push(Vec::new());
    }

    let mut num = mht.len();
    let mut p = mht.len();
    let mut data_view: &[u8] = data;

    for i in 0..deep {
        let loc: u8;
        let sibling: &[u8];
        if (index + 1) % 2 == 0 {
            loc = 0;
            sibling = &data_view[(index - 1) * size..index * size];
        } else {
            loc = 1;
            sibling = &data_view[(index + 1) * size..(index + 2) * size];
        }
        if i == 0 && (size != DEFAULT_HASH_SIZE || !hashed) {
            let mut hasher = Sha256::new();
            hasher.update(sibling);
            proof.path[i] = hasher.finalize().to_vec();
            size = DEFAULT_HASH_SIZE;
        } else {
            proof.path[i] = sibling.to_vec();
        }
        proof.locs[i] = loc;
        num /= 2;
        index /= 2;
        p -= num;
        data_view = &mht[p..p + num];
    }
    Ok(proof)
}

/// Generates a path proof when only a slice of the tree is materialised
/// and an `aux` cache covers the top of the tree.
///
/// This avoids materialising a tree over all `data` for large files.
pub fn get_path_proof_with_aux(
    data: &[u8],
    aux: &[u8],
    index: usize,
    size: usize,
) -> anyhow::Result<PathProof> {
    let aux_size = aux.len() / DEFAULT_HASH_SIZE;
    if aux_size == 0 {
        return Ok(PathProof::default());
    }
    let plate_size = data.len() / size / aux_size;
    let mut mht = vec![0u8; plate_size * DEFAULT_HASH_SIZE];
    let left = index / plate_size;
    let plate_data = &data[left * plate_size * size..(left + 1) * plate_size * size];
    let mut hasher = Sha256::new();
    for i in 0..plate_size {
        hasher.update(&plate_data[i * size..(i + 1) * size]);
        let result = hasher.finalize_reset();
        mht[i * DEFAULT_HASH_SIZE..(i + 1) * DEFAULT_HASH_SIZE].copy_from_slice(&result);
    }
    calc_light_mht(&mut mht);

    let mut sub_proof = get_path_proof_inner(&mht, plate_data, index % plate_size, size, false)?;

    let mut top_mht = vec![0u8; aux.len()];
    top_mht[..aux.len()].copy_from_slice(aux);
    calc_light_mht(&mut top_mht);
    let top_proof = get_path_proof_inner(&top_mht, aux, left, DEFAULT_HASH_SIZE, true)?;

    sub_proof.locs.extend(top_proof.locs);
    sub_proof.path.extend(top_proof.path);
    Ok(sub_proof)
}

// -----------------------------------------------------------------------------
// Verification helpers
// -----------------------------------------------------------------------------

/// Verifies that `data` is a leaf whose path proof produces `root`.
pub fn verify_path_proof(root: &[u8], data: &[u8], proof: PathProof) -> bool {
    if proof.locs.len() != proof.path.len() {
        return false;
    }
    let mut hasher = Sha256::new();
    hasher.update(data);
    let mut acc = hasher.finalize_reset().to_vec();
    if acc.len() != root.len() {
        return false;
    }
    for i in 0..proof.path.len() {
        if proof.locs[i] == 0 {
            hasher.update(&proof.path[i]);
            hasher.update(&acc);
        } else {
            hasher.update(&acc);
            hasher.update(&proof.path[i]);
        }
        acc = hasher.finalize_reset().to_vec();
    }
    root == acc.as_slice()
}

/// Sanity-check that a location vector encodes the binary expansion of `index`.
pub fn check_index_path(mut index: i64, locs: &[u8]) -> bool {
    for v in locs {
        if (index + 1) % 2 == 0 {
            if *v != 0 {
                return false;
            }
        } else if *v != 1 {
            return false;
        }
        index /= 2;
    }
    true
}
