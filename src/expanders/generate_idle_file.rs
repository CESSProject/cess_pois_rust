//! # Idle-File Generation
//!
//! Builds the directory tree of idle-file labels that backs the
//! Proof-of-Idle-Space.  Mirrors `expanders/generate_idle_file.go`
//! in the Go reference implementation.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use sha2::{Digest, Sha256, Sha512};

use crate::tree::{
    calc_light_mht_with_bytes, get_light_mht_from_pool, get_root, put_light_mht_to_pool,
    DEFAULT_HASH_SIZE,
};
use crate::util::{add_data, clear_data, copy_data, read_file_to_buf, save_file, save_proof_file};

use super::generate_expanders::calc_parents;
use super::{get_bytes, Expanders, Node, NodeType};

// -----------------------------------------------------------------------------
// Constants
// -----------------------------------------------------------------------------

pub const DEFAULT_IDLE_FILES_PATH: &str = "./proofs";
pub const FILE_NAME: &str = "sub-file";
pub const COMMIT_FILE: &str = "file-roots";
pub const CLUSTER_DIR_NAME: &str = "file-cluster";
pub const SET_DIR_NAME: &str = "idle-files";
pub const AUX_FILE: &str = "aux-file";
pub const DEFAULT_AUX_SIZE: usize = 64;

/// Output size (in bytes) of the selected node-label hash.
///
/// Supported values match the Go reference:
/// - `32` → SHA-256
/// - `64` → SHA-512
///
/// Any other value defaults to SHA-512.
pub const HASH_SIZE: i32 = 64;

/// Supported hash algorithms used for node labels.
pub enum Hasher {
    SHA256(Sha256),
    SHA512(Sha512),
}

/// Returns a fresh node-label hasher matching [`HASH_SIZE`].
pub fn new_hash() -> Hasher {
    match HASH_SIZE {
        32 => Hasher::SHA256(Sha256::new()),
        64 => Hasher::SHA512(Sha512::new()),
        _ => Hasher::SHA512(Sha512::new()),
    }
}

/// One-shot hash convenience helper used by callers that just need a digest.
pub fn get_hash(data: &[u8]) -> Vec<u8> {
    let mut data = data;
    if data.is_empty() {
        data = b"none";
    }
    match new_hash() {
        Hasher::SHA256(mut h) => {
            h.update(data);
            h.finalize().to_vec()
        }
        Hasher::SHA512(mut h) => {
            h.update(data);
            h.finalize().to_vec()
        }
    }
}

/// Updates a hasher with `data`.
fn hasher_update(h: &mut Hasher, data: &[u8]) {
    match h {
        Hasher::SHA256(h) => h.update(data),
        Hasher::SHA512(h) => h.update(data),
    }
}

/// Finalises and returns the digest bytes, leaving the hasher reset and reusable.
fn hasher_finalize_reset(h: &mut Hasher) -> Vec<u8> {
    match h {
        Hasher::SHA256(h) => h.finalize_reset().to_vec(),
        Hasher::SHA512(h) => h.finalize_reset().to_vec(),
    }
}

/// (Re)creates `dir`, removing any existing contents.
pub fn make_proof_dir<P: AsRef<Path>>(dir: P) -> Result<()> {
    let dir = dir.as_ref();
    if dir.exists() {
        std::fs::remove_dir_all(dir).with_context(|| "make proof dir: cleanup error")?;
    }
    std::fs::create_dir_all(dir).with_context(|| "make proof dir: create error")?;
    Ok(())
}

/// Helper: pre-computes parent lists for the `n` nodes in a single layer.
///
/// Replaces Go's channel-based `calcNodesParents` goroutine — since each
/// parent computation is CPU-local and independent we just batch them up.
fn calc_layer_parents(
    expanders: &Expanders,
    layer: i64,
    miner_id: &[u8],
    count: i64,
) -> Vec<Node> {
    let logical_layer = if layer >= expanders.k {
        expanders.k
    } else {
        layer
    };
    let mut nodes = Vec::with_capacity(expanders.n as usize);
    for j in 0..expanders.n {
        let mut node = Node::with_capacity(
            (j + logical_layer * expanders.n) as NodeType,
            expanders.d,
        );
        calc_parents(expanders, &mut node, miner_id, count, layer);
        nodes.push(node);
    }
    nodes
}

/// Loads elder-layer data (read & XOR-merged) into `elders`.
fn read_elders_data(
    expanders: &Expanders,
    set_dir: &Path,
    layer: i64,
    cidx: usize,
    elders: &mut [u8],
    clusters: &[i64],
) -> Result<()> {
    let base_layer = ((layer - expanders.k / 2) / expanders.k) as i64;
    clear_data(elders);
    let mut temp = vec![0u8; elders.len()];
    for l in 0..(expanders.k / 2) as i64 {
        let p = set_dir
            .join(format!("{}-{}", CLUSTER_DIR_NAME, clusters[cidx]))
            .join(format!("{}-{}", FILE_NAME, base_layer + 2 * l));
        read_file_to_buf(&p, &mut temp).with_context(|| "read elders' data error")?;
        add_data(elders, &[&temp]);
    }
    Ok(())
}

impl Expanders {
    /// Builds a contiguous set of `size` idle file clusters under `root_dir`.
    ///
    /// This is **not** thread-safe — callers wishing to generate multiple
    /// sets in parallel should invoke this once per OS thread on disjoint
    /// `start` ranges.
    pub fn generate_idle_file_set(
        &self,
        miner_id: &[u8],
        start: i64,
        size: i64,
        root_dir: &str,
    ) -> Result<()> {
        let hash_size = HASH_SIZE as usize;

        // ----- directory layout -----
        let mut clusters: Vec<i64> = Vec::with_capacity(size as usize);
        let set_dir = PathBuf::from(root_dir).join(format!("{}-{}", SET_DIR_NAME, (start + size) / size));
        for i in start..start + size {
            let dir = set_dir.join(format!("{}-{}", CLUSTER_DIR_NAME, i));
            make_proof_dir(&dir).with_context(|| "generate idle file error")?;
            clusters.push(i);
        }

        let file_num = self.k; // files per cluster (logical-K)
        let roots_len = ((self.k + file_num) * size + 1) as usize;
        let mut roots: Vec<Vec<u8>> = vec![Vec::new(); roots_len];

        let buf_len = self.n as usize * hash_size;
        let mut elders = vec![0u8; buf_len];
        let mut parents = vec![0u8; buf_len];
        let mut labels = vec![0u8; buf_len];
        let mut mht = get_light_mht_from_pool();
        // ensure the mht buffer is large enough for this expander's leaves
        if mht.len() != self.n as usize * DEFAULT_HASH_SIZE {
            put_light_mht_to_pool(mht);
            mht = vec![0u8; self.n as usize * DEFAULT_HASH_SIZE];
        }
        let mut aux = vec![0u8; DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE];

        // ----- label layout: [minerID || clusterID || fileID || nodeID || parents || file_deps] -----
        let front_size = miner_id.len() + std::mem::size_of::<NodeType>() + 8 + 8;
        let mut label = vec![0u8; front_size + 2 * hash_size];
        // miner_id is fixed for the whole set
        copy_data(&mut label, &[miner_id]);

        for i in 0..(self.k + file_num) {
            let mut logical_layer = i;
            for j in 0..size as usize {
                // Update clusterID + (zero) fileID prefix once per cluster.
                copy_data(
                    &mut label[miner_id.len()..],
                    &[&get_bytes(clusters[j]), &get_bytes(0i64)],
                );

                // Pre-compute parent metadata for the n nodes at this layer.
                let layer_nodes = calc_layer_parents(self, i, miner_id, clusters[j]);

                // When we cross into the upper K layers, encode fileID + load elders.
                if i >= self.k {
                    logical_layer = self.k;
                    let file_id = (clusters[j] - 1) * file_num + i - self.k + 1;
                    copy_data(
                        &mut label[miner_id.len() + 8..],
                        &[&get_bytes(file_id)],
                    );
                    read_elders_data(self, &set_dir, i, j, &mut elders, &clusters)?;
                }

                // Load the previous layer's labels (the "parents" buffer).
                if i > 0 {
                    let p = set_dir
                        .join(format!("{}-{}", CLUSTER_DIR_NAME, clusters[j]))
                        .join(format!("{}-{}", FILE_NAME, logical_layer - 1));
                    read_file_to_buf(&p, &mut parents)
                        .with_context(|| "generate idle file error")?;
                }

                let mut node_hasher = new_hash();

                for k in 0..self.n {
                    // Update nodeID portion of label.
                    let node_idx_val: NodeType = (logical_layer * self.n + k) as NodeType;
                    copy_data(
                        &mut label[miner_id.len() + 8 + 8..],
                        &[&get_bytes(node_idx_val)],
                    );
                    // Clear the parents+deps tail.
                    clear_data(&mut label[front_size..]);

                    let node = &layer_nodes[k as usize];
                    if i > 0 && !node.no_parents() {
                        for &pidx in &node.parents {
                            let idx = (pidx as i64) % self.n;
                            let l = (idx * hash_size as i64) as usize;
                            let r = ((idx + 1) * hash_size as i64) as usize;
                            if (pidx as i64) < logical_layer * self.n {
                                add_data(
                                    &mut label[front_size..front_size + hash_size],
                                    &[&parents[l..r]],
                                );
                            } else {
                                add_data(
                                    &mut label[front_size..front_size + hash_size],
                                    &[&labels[l..r]],
                                );
                            }
                        }
                        // upper-layer file dependency
                        if i >= self.k {
                            let lo = (k * hash_size as i64) as usize;
                            let hi = ((k + 1) * hash_size as i64) as usize;
                            add_data(
                                &mut label[front_size + hash_size..front_size + 2 * hash_size],
                                &[&elders[lo..hi]],
                            );
                        }
                    }

                    hasher_update(&mut node_hasher, &label);
                    if i + (j as i64) > 0 {
                        // same-layer dependency on previous node
                        let lo = (k * hash_size as i64) as usize;
                        let hi = ((k + 1) * hash_size as i64) as usize;
                        hasher_update(&mut node_hasher, &labels[lo..hi]);
                    }
                    let h = hasher_finalize_reset(&mut node_hasher);
                    let lo = (k * hash_size as i64) as usize;
                    let hi = ((k + 1) * hash_size as i64) as usize;
                    labels[lo..hi].copy_from_slice(&h);
                }

                // ----- per-file Merkle root -----
                calc_light_mht_with_bytes(&mut mht, &labels, hash_size);
                let root_idx = (i * size + j as i64) as usize;
                roots[root_idx] = get_root(&mht);
                // Cache the upper portion of the tree as aux data.
                let aux_src_start = DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE;
                let aux_src_end = 2 * DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE;
                if mht.len() >= aux_src_end {
                    aux.copy_from_slice(&mht[aux_src_start..aux_src_end]);
                }

                // ----- persist aux + labels -----
                let cluster_dir = set_dir.join(format!("{}-{}", CLUSTER_DIR_NAME, clusters[j]));
                save_file(cluster_dir.join(format!("{}-{}", AUX_FILE, i)), &aux)
                    .with_context(|| "generate idle file error")?;
                save_file(cluster_dir.join(format!("{}-{}", FILE_NAME, i)), &labels)
                    .with_context(|| "generate idle file error")?;
            }
        }

        put_light_mht_to_pool(mht);

        // ----- aggregate root over all per-file roots -----
        let mut agg = Sha256::new();
        for r in roots.iter().take(roots.len() - 1) {
            agg.update(r);
        }
        let last = agg.finalize();
        roots[((self.k + file_num) * size) as usize] = last.to_vec();

        save_proof_file(set_dir.join(COMMIT_FILE), &roots)
            .with_context(|| "generate idle file error")?;
        Ok(())
    }
}
