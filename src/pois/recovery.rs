//! # Prover Recovery Routines
//!
//! Mirrors `pois/recovery.go`.  Provides helpers to:
//! - Regenerate damaged idle files
//! - Recompute and restore sub-accumulator state
//! - Scan the on-disk layout in batch / parallel

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use rayon::prelude::*;

use crate::acc::file_manage::{DEFAULT_ELEMS_NUM, DEFAULT_NAME};
use crate::expanders::generate_idle_file::{get_hash, DEFAULT_AUX_SIZE, SET_DIR_NAME};
use crate::expanders::get_bytes;
use crate::tree::{calc_light_mht_with_aux, get_root, DEFAULT_HASH_SIZE};
use crate::util::read_file_to_buf;

use super::prover::Prover;

impl Prover {
    /// Regenerates raw idle files for `set_id`, then runs `organize_files`
    /// to clear intermediate layers.
    pub fn restore_idle_files(self: &Arc<Self>, set_id: i64) -> Result<()> {
        self.restore_raw_idle_files(set_id)
            .with_context(|| "restore idle files error")?;
        let s = { self.state.read().clone() };
        let file_num = s.cluster_size * s.set_len;
        self.organize_files_pub(set_id * file_num, file_num)
            .with_context(|| "restore idle files error")
    }

    /// Regenerates raw idle files for `set_id` without organizing.
    pub fn restore_raw_idle_files(self: &Arc<Self>, set_id: i64) -> Result<()> {
        if set_id < 1 {
            bail!("restore raw idle files error: file set id error");
        }
        let (set_len, cluster_size, space, file_size, idle_file_path) = {
            let s = { self.state.read().clone() };
            let cfg = self
                .config_clone_basic()
                .ok_or_else(|| anyhow!("config not set"))?;
            (s.set_len, s.cluster_size, s.space, cfg.3, cfg.2)
        };
        let file_num = set_len * cluster_size;
        if space < (file_num + set_len * self.expanders.k) * file_size {
            bail!("restore raw idle files error: not enough space");
        }
        let start = (set_id - 1) * 256 / cluster_size + 1;
        self.expanders
            .generate_idle_file_set(&self.id, start, set_len, &idle_file_path)
            .with_context(|| "restore raw idle files error")
    }

    /// Restores a single sub-accumulator file for `set_id`.
    pub fn restore_sub_acc_files(self: &Arc<Self>, set_id: i64) -> Result<()> {
        let s = { self.state.read().clone() };
        let rear = set_id * s.cluster_size * s.set_len;
        if rear > s.rear || rear <= 0 {
            bail!("restore sub acc files error: bad set id");
        }
        let roots = match self.check_files_and_get_tree_roots(set_id) {
            Ok(r) => r,
            Err(_) => Vec::new(),
        };
        let roots = if roots.len() != DEFAULT_ELEMS_NUM {
            self.restore_idle_files(set_id)
                .with_context(|| "restore sub acc files error")?;
            self.check_files_and_get_tree_roots(set_id)
                .with_context(|| "restore sub acc files error")?
        } else {
            roots
        };

        let mut labels: Vec<Vec<u8>> = Vec::with_capacity(roots.len());
        let offset = (set_id - 1) * s.set_len * s.cluster_size;
        for (i, root) in roots.iter().enumerate() {
            let mut label = Vec::with_capacity(self.id.len() + 8 + root.len());
            label.extend_from_slice(&self.id);
            label.extend_from_slice(&get_bytes(offset + i as i64 + 1));
            label.extend_from_slice(root);
            labels.push(get_hash(&label));
        }
        let mgr = self
            .acc_manager
            .read()
            .clone()
            .ok_or_else(|| anyhow!("acc manager not initialised"))?;
        mgr.restore_sub_acc_file(set_id - 1, labels)
            .with_context(|| "restore sub acc files error")
    }

    /// Verifies that all sub-accumulator files exist in `[front, rear]`.
    /// Any missing file triggers a recomputation.
    pub fn check_and_restore_sub_acc_files(
        self: &Arc<Self>,
        front: i64,
        rear: i64,
    ) -> Result<()> {
        if front < 0 || front > rear {
            bail!("check and restore sub acc files error: bad front and rear value");
        }
        let start = front / DEFAULT_ELEMS_NUM as i64 + 1;
        let end = rear / DEFAULT_ELEMS_NUM as i64;
        let mgr = self
            .acc_manager
            .read()
            .clone()
            .ok_or_else(|| anyhow!("acc manager not initialised"))?;
        let acc_dir = mgr.get_file_path();
        for i in start..=end {
            let fpath = Path::new(&acc_dir).join(format!("{}-{}", DEFAULT_NAME, i - 1));
            if fpath.exists() {
                continue;
            }
            self.restore_sub_acc_files(i)
                .with_context(|| "check and restore sub acc files error")?;
        }
        Ok(())
    }

    /// Parallel variant of `check_and_restore_sub_acc_files`.
    pub fn check_and_restore_idle_data(
        self: &Arc<Self>,
        front: i64,
        rear: i64,
        t_num: usize,
    ) -> Result<()> {
        let _ = t_num; // rayon decides the pool size, but we accept the param for API parity
        if front < 0 || front > rear {
            bail!("check and restore sub acc files error: bad front and rear value");
        }
        let start = front / DEFAULT_ELEMS_NUM as i64 + 1;
        let end = rear / DEFAULT_ELEMS_NUM as i64;
        let mgr = self
            .acc_manager
            .read()
            .clone()
            .ok_or_else(|| anyhow!("acc manager not initialised"))?;
        let acc_dir = mgr.get_file_path();
        let prover = self.clone();
        let results: Vec<Result<()>> = (start..=end)
            .into_par_iter()
            .map(|i| {
                let fpath = Path::new(&acc_dir).join(format!("{}-{}", DEFAULT_NAME, i - 1));
                if fpath.exists() {
                    return Ok(());
                }
                prover
                    .restore_sub_acc_files(i)
                    .with_context(|| "check and restore sub acc files error")
            })
            .collect();
        results
            .into_iter()
            .find_map(|r| r.err())
            .map(Err)
            .unwrap_or(Ok(()))
    }

    /// Reads the aux files for `set_id` and produces the Merkle roots
    /// for each cluster's last `K` files.
    pub fn check_files_and_get_tree_roots(
        self: &Arc<Self>,
        set_id: i64,
    ) -> Result<Vec<Vec<u8>>> {
        let (set_len, cluster_size, idle_file_path) = {
            let s = { self.state.read().clone() };
            let cfg = self
                .config_clone_basic()
                .ok_or_else(|| anyhow!("config not set"))?;
            (s.set_len, s.cluster_size, cfg.2)
        };
        let files_dir =
            PathBuf::from(&idle_file_path).join(format!("{}-{}", SET_DIR_NAME, set_id));
        let aux_size = DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE;
        let mut roots: Vec<Vec<u8>> = Vec::with_capacity(DEFAULT_ELEMS_NUM);
        let mut mht = vec![0u8; aux_size];

        let mut entries: Vec<_> = std::fs::read_dir(&files_dir)
            .with_context(|| "read files dir error")?
            .filter_map(|e| e.ok())
            .collect();
        entries.sort_by_key(|e| dir_entry_index(&e.file_name().to_string_lossy()));

        for entry in &entries {
            if !entry.path().is_dir() {
                continue;
            }
            let mut cluster_entries: Vec<_> = std::fs::read_dir(entry.path())
                .with_context(|| "read cluster dir error")?
                .filter_map(|e| e.ok())
                .collect();
            cluster_entries.sort_by_key(|e| dir_entry_index(&e.file_name().to_string_lossy()));

            for file in &cluster_entries {
                let meta = file.metadata().with_context(|| "stat file error")?;
                if meta.is_dir() || meta.len() as usize != aux_size {
                    continue;
                }
                let name = file.file_name();
                let name = name.to_string_lossy();
                let index: i64 = match name.split('-').last().and_then(|s| s.parse().ok()) {
                    Some(v) => v,
                    None => continue,
                };
                if index < self.expanders.k {
                    continue;
                }
                let mut aux = vec![0u8; aux_size];
                read_file_to_buf(file.path(), &mut aux)?;
                calc_light_mht_with_aux(&mut mht, &aux);
                roots.push(get_root(&mht));
            }
        }
        if roots.len() != (set_len * cluster_size) as usize {
            bail!("error root number");
        }
        Ok(roots)
    }

    // -----------------------------------------------------------------------
    // Internal accessors needed because the prover state is private to
    // `prover.rs`.  This crate-private helper extends [`Prover`] just
    // enough for recovery.
    // -----------------------------------------------------------------------

    pub(crate) fn organize_files_pub(self: &Arc<Self>, idx: i64, num: i64) -> Result<()> {
        self.organize_files(idx, num)
    }

    pub(crate) fn config_clone_basic(self: &Arc<Self>) -> Option<(String, String, String, i64)> {
        let cfg = self.config.read();
        cfg.as_ref().map(|c| {
            (
                c.acc_path.clone(),
                c.chall_acc_path.clone(),
                c.idle_file_path.clone(),
                c.file_size,
            )
        })
    }
}

/// Parses the trailing "-N" suffix out of a directory or filename.
fn dir_entry_index(name: &str) -> i64 {
    name.rsplit('-')
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(i64::MAX)
}
