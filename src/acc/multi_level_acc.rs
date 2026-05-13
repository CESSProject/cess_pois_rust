//! # Multi-Level RSA Accumulator
//!
//! Implements both:
//! 1. The verifier-side checks on multi-level witness chains
//!    (`verify_mutilevel_acc`, `verify_insert_update`,
//!    `verify_delete_update`, `verify_mutilevel_acc_for_batch`).
//! 2. The full prover-side stateful tree (`MutiLevelAcc`) with
//!    snapshot/rollback semantics, on-disk persistence and proof generation.
//!
//! Mirrors `acc/muti_level_acc.go` in the Go reference.

use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use num_bigint_dig::BigUint;
use parking_lot::RwLock;
use rand::Rng;
use serde::{Deserialize, Serialize};

use super::file_manage::{
    backup_acc_data, delete_acc_data, ensure_dir, read_acc_data, read_backup, recovery_acc_data,
    save_acc_data, AccData, DEFAULT_ELEMS_NUM, DEFAULT_LEVEL, DEFAULT_PATH,
};
use super::hash_2_prime::h_prime;
use super::{
    gen_wits_for_acc_nodes, generate_acc, generate_witness, RsaKey,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Maximum time AddElements/DeleteElements is allowed to wait on the
/// shared update lock before bailing.
const TIMEOUT: Duration = Duration::from_secs(120);

// ---------------------------------------------------------------------------
// Data structures
// ---------------------------------------------------------------------------

/// A node in the in-memory accumulator tree.
///
/// Each node holds:
/// - `value`: the accumulator value at this node
/// - `children`: the child sub-accumulators (or leaves)
/// - `len`: child count (denormalized — matches the Go field)
/// - `wit`: witness used by this node's parent
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct AccNode {
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub value: Vec<u8>,
    #[serde(default)]
    pub children: Vec<AccNode>,
    #[serde(default)]
    pub len: usize,
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub wit: Vec<u8>,
}

/// A node in a multi-level accumulator witness chain.
///
/// JSON layout matches Go's `acc.WitnessNode` (base64-encoded byte fields).
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct WitnessNode {
    /// Element value (or accumulator value, at higher levels).
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub elem: Vec<u8>,
    /// Witness proving membership at this level.
    #[serde(default, with = "crate::util::json_bytes::bytes")]
    pub wit: Vec<u8>,
    /// Optional parent accumulator witness node.
    pub acc: Option<Box<WitnessNode>>,
}

/// Snapshot-friendly view of the multi-level accumulator.
#[derive(Clone, Debug)]
pub struct AccSnapshot {
    pub accs: AccNode,
    pub elem_nums: usize,
    pub curr_count: usize,
    pub deleted: usize,
    pub file_path: String,
    pub key: RsaKey,
}

/// Stateful multi-level accumulator (prover-side).
///
/// Wraps the tree in a [`RwLock`] for fine-grained access.  Updates use
/// the `is_update` / `stable` flags to serialise modifications.
pub struct MutiLevelAcc {
    inner: RwLock<MutiLevelAccInner>,
    file_path: String,
    pub key: RsaKey,
    /// Whether a deletion is currently in-flight.
    pub is_del: Arc<AtomicBool>,
}

struct MutiLevelAccInner {
    accs: AccNode,
    elem_nums: usize,
    deleted: usize,
    curr_count: usize,
    is_update: bool,
    stable: bool,
    snapshot: Option<AccSnapshot>,
}

// ---------------------------------------------------------------------------
// Constructors & recovery
// ---------------------------------------------------------------------------

impl MutiLevelAcc {
    /// Creates a brand-new multi-level accumulator under `path`.
    pub fn new(path: &str, key: RsaKey) -> Result<Arc<Self>> {
        let path = if path.is_empty() {
            DEFAULT_PATH.to_string()
        } else {
            path.to_string()
        };
        ensure_dir(&path).with_context(|| "create acc dir error")?;
        let accs = AccNode {
            value: key.g.to_bytes_be(),
            ..Default::default()
        };
        let acc = MutiLevelAcc {
            inner: RwLock::new(MutiLevelAccInner {
                accs,
                elem_nums: 0,
                deleted: 0,
                curr_count: 0,
                is_update: false,
                stable: true,
                snapshot: None,
            }),
            file_path: path,
            key,
            is_del: Arc::new(AtomicBool::new(false)),
        };
        Ok(Arc::new(acc))
    }

    /// Reconstructs the multi-level accumulator from existing sub-acc files.
    pub fn recovery(acc_path: &str, key: RsaKey, front: i64, rear: i64) -> Result<Arc<Self>> {
        let path = if acc_path.is_empty() {
            DEFAULT_PATH.to_string()
        } else {
            acc_path.to_string()
        };
        ensure_dir(&path).with_context(|| "recovery muti-acc error")?;

        let accs = AccNode {
            value: key.g.to_bytes_be(),
            ..Default::default()
        };

        let acc = Arc::new(MutiLevelAcc {
            inner: RwLock::new(MutiLevelAccInner {
                accs,
                elem_nums: 0,
                deleted: front as usize,
                curr_count: 0,
                is_update: false,
                stable: true,
                snapshot: None,
            }),
            file_path: path,
            key,
            is_del: Arc::new(AtomicBool::new(false)),
        });

        acc.construct_muti_acc(rear)
            .with_context(|| "recovery muti-acc error")?;
        Ok(acc)
    }

    pub fn get_file_path(&self) -> String {
        self.file_path.clone()
    }

    // -----------------------------------------------------------------------
    // Snapshots
    // -----------------------------------------------------------------------

    /// Returns the current snapshot of the accumulator (creating one if needed).
    pub fn get_snapshot(&self) -> AccSnapshot {
        let snap = {
            let inner = self.inner.read();
            inner.snapshot.clone()
        };
        if let Some(snap) = snap {
            return snap;
        }
        // Need a write-lock to populate.
        let mut inner = self.inner.write();
        if inner.snapshot.is_none() {
            inner.snapshot = Some(self.snapshot_of(&inner));
        }
        inner.snapshot.clone().unwrap()
    }

    /// Refreshes the snapshot post-update.
    pub fn update_snapshot(&self) -> bool {
        let mut inner = self.inner.write();
        if inner.is_update {
            return false;
        }
        inner.snapshot = Some(self.snapshot_of(&inner));
        inner.stable = true;
        true
    }

    /// Reverts to the last snapshot and restores any disk backups.
    pub fn rollback(&self) -> bool {
        let mut inner = self.inner.write();
        if inner.is_update || inner.snapshot.is_none() {
            return false;
        }
        let snap = inner.snapshot.clone().unwrap();
        if inner.deleted != snap.deleted {
            if recovery_acc_data(&self.file_path, (inner.deleted / DEFAULT_ELEMS_NUM) as i64).is_err()
            {
                return false;
            }
        }
        inner.accs = snap.accs.clone();
        inner.elem_nums = snap.elem_nums;
        inner.deleted = snap.deleted;
        inner.curr_count = snap.curr_count;
        inner.stable = true;
        true
    }

    fn snapshot_of(&self, inner: &MutiLevelAccInner) -> AccSnapshot {
        AccSnapshot {
            accs: inner.accs.clone(),
            elem_nums: inner.elem_nums,
            curr_count: inner.curr_count,
            deleted: inner.deleted,
            file_path: self.file_path.clone(),
            key: self.key.clone(),
        }
    }

    /// Try to acquire the update lock.  Returns `true` if a snapshot was taken
    /// (or released).  Mirrors `setUpdate` in Go.
    fn set_update(&self, yes: bool) -> bool {
        let mut inner = self.inner.write();
        if yes {
            if inner.is_update || !inner.stable {
                return false;
            }
            inner.snapshot = Some(self.snapshot_of(&inner));
            inner.is_update = true;
            inner.stable = false;
            return true;
        }
        inner.is_update = false;
        true
    }

    // -----------------------------------------------------------------------
    // Reads
    // -----------------------------------------------------------------------

    /// Returns the current top-level accumulator value.
    pub fn current_acc_value(&self) -> Vec<u8> {
        self.inner.read().accs.value.clone()
    }

    /// Returns `(deleted, elem_nums, curr_count)`.
    pub fn counters(&self) -> (usize, usize, usize) {
        let inner = self.inner.read();
        (inner.deleted, inner.elem_nums, inner.curr_count)
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

impl MutiLevelAcc {
    /// Refreshes a single node's witness vector and accumulator value.
    fn update_acc(&self, node: &mut AccNode) {
        let lens = node.children.len();
        node.len = lens;
        if lens == 0 {
            node.value = self.key.g.to_bytes_be();
            node.wit = Vec::new();
            return;
        }
        gen_wits_for_acc_nodes(&self.key.g, &self.key.n, &mut node.children);
        let last = &node.children[lens - 1];
        node.value = generate_acc(&self.key, &last.wit, vec![last.value.clone()]).unwrap_or_default();
    }

    /// Inserts a constructed sub-accumulator into the tree.
    fn add_sub_acc(&self, inner: &mut MutiLevelAccInner, mut sub_acc: AccNode) {
        if inner.curr_count == 0 {
            let g = self.key.g.to_bytes_be();
            sub_acc.wit = g.clone();
            inner.curr_count = sub_acc.len;
            let parent = AccNode {
                value: generate_acc(&self.key, &g, vec![sub_acc.value.clone()]).unwrap_or_default(),
                wit: g.clone(),
                len: 1,
                children: vec![sub_acc],
            };
            inner.accs = AccNode {
                value: generate_acc(&self.key, &g, vec![parent.value.clone()]).unwrap_or_default(),
                wit: Vec::new(),
                len: 1,
                children: vec![parent],
            };
            inner.elem_nums += inner.curr_count;
            return;
        }

        let curr_count = inner.curr_count;
        let parent_children_len = inner.accs.children[inner.accs.children.len() - 1].children.len();
        if curr_count > 0 && curr_count < DEFAULT_ELEMS_NUM {
            inner.elem_nums += sub_acc.len - curr_count;
            let parent_idx = inner.accs.children.len() - 1;
            let last_child = inner.accs.children[parent_idx].children.len() - 1;
            inner.accs.children[parent_idx].children[last_child] = sub_acc.clone();
        } else if parent_children_len + 1 <= DEFAULT_ELEMS_NUM {
            inner.elem_nums += sub_acc.len;
            let parent_idx = inner.accs.children.len() - 1;
            inner.accs.children[parent_idx].children.push(sub_acc.clone());
        } else {
            inner.elem_nums += sub_acc.len;
            let new_parent = AccNode {
                wit: self.key.g.to_bytes_be(),
                children: vec![sub_acc.clone()],
                len: 1,
                value: Vec::new(),
            };
            inner.accs.children.push(new_parent);
        }
        inner.curr_count = sub_acc.len;
        let parent_idx = inner.accs.children.len() - 1;
        let parent = &mut inner.accs.children[parent_idx];
        self.update_acc(parent);
        // re-take a mutable borrow of the root
        let mut root = std::mem::take(&mut inner.accs);
        self.update_acc(&mut root);
        inner.accs = root;
    }

    /// Lazy variant that defers witness/acc updates to the caller.
    fn add_sub_acc_by_batch(&self, inner: &mut MutiLevelAccInner, sub_acc: AccNode) {
        if inner.curr_count == 0 {
            inner.curr_count = sub_acc.len;
            let parent = AccNode {
                children: vec![sub_acc],
                len: 1,
                ..Default::default()
            };
            inner.accs = AccNode {
                children: vec![parent],
                len: 1,
                ..Default::default()
            };
            inner.elem_nums += inner.curr_count;
            return;
        }
        let curr_count = inner.curr_count;
        let parent_children_len = inner.accs.children[inner.accs.children.len() - 1].children.len();
        if curr_count > 0 && curr_count < DEFAULT_ELEMS_NUM {
            inner.elem_nums += sub_acc.len - curr_count;
            let parent_idx = inner.accs.children.len() - 1;
            let last_child = inner.accs.children[parent_idx].children.len() - 1;
            inner.accs.children[parent_idx].children[last_child] = sub_acc.clone();
        } else if parent_children_len + 1 <= DEFAULT_ELEMS_NUM {
            inner.elem_nums += sub_acc.len;
            let parent_idx = inner.accs.children.len() - 1;
            inner.accs.children[parent_idx].children.push(sub_acc.clone());
        } else {
            inner.elem_nums += sub_acc.len;
            let new_parent = AccNode {
                children: vec![sub_acc.clone()],
                len: 1,
                ..Default::default()
            };
            inner.accs.children.push(new_parent);
        }
        inner.curr_count = sub_acc.len;
    }

    /// Adds `elems` to the bottom-level sub-accumulator.
    fn add_elements_inner(&self, inner: &mut MutiLevelAccInner, elems: Vec<Vec<u8>>) -> Result<AccNode> {
        let mut data: AccData;
        if inner.curr_count > 0 && inner.curr_count < DEFAULT_ELEMS_NUM {
            let index = ((inner.deleted + inner.elem_nums - 1) / DEFAULT_ELEMS_NUM) as i64;
            data = read_acc_data(&self.file_path, index)
                .with_context(|| "add elements to sub acc error")?;
            data.values.extend(elems.clone());
        } else {
            data = AccData {
                values: elems.clone(),
                wits: Vec::new(),
            };
        }
        data.wits = generate_witness(&self.key.g, &self.key.n, &data.values);
        let len = data.values.len();
        let value = generate_acc(
            &self.key,
            &data.wits[len - 1],
            vec![data.values[len - 1].clone()],
        )
        .unwrap_or_default();

        let index =
            ((inner.deleted + inner.elem_nums + elems.len() - 1) / DEFAULT_ELEMS_NUM) as i64;
        save_acc_data(&self.file_path, index, data.values.clone(), data.wits.clone())
            .with_context(|| "add elements to sub acc error")?;

        Ok(AccNode {
            value,
            len,
            ..Default::default()
        })
    }
}

// ---------------------------------------------------------------------------
// Public add/delete entry points
// ---------------------------------------------------------------------------

impl MutiLevelAcc {
    /// Restores a sub-accumulator file given `index` and a fixed-size element batch.
    pub fn restore_sub_acc_file(&self, index: i64, elems: Vec<Vec<u8>>) -> Result<()> {
        if elems.len() != DEFAULT_ELEMS_NUM {
            bail!("wrong number of elements");
        }
        let wits = generate_witness(&self.key.g, &self.key.n, &elems);
        save_acc_data(&self.file_path, index, elems, wits)?;
        Ok(())
    }

    /// Adds `elems` to the accumulator and updates the upper levels.
    pub fn add_elements(&self, elems: Vec<Vec<u8>>) -> Result<()> {
        let mut inner = self.inner.write();
        let lens = elems.len();
        if lens == 0
            || (inner.curr_count < DEFAULT_ELEMS_NUM
                && lens + inner.curr_count > DEFAULT_ELEMS_NUM)
        {
            bail!("add elements error: illegal number of elements");
        }
        let new_acc = self
            .add_elements_inner(&mut inner, elems)
            .with_context(|| "add elements error")?;
        self.add_sub_acc(&mut inner, new_acc);
        Ok(())
    }

    /// Deletes the first `num` elements of the bottom-level sub-accumulator.
    pub fn delete_elements(&self, num: usize) -> Result<()> {
        let mut inner = self.inner.write();
        let index = (inner.deleted / DEFAULT_ELEMS_NUM) as i64;
        let offset = inner.deleted % DEFAULT_ELEMS_NUM;
        if num == 0 || num > inner.elem_nums || num + offset > DEFAULT_ELEMS_NUM {
            bail!("delete elements error: illegal number of elements");
        }

        let mut data = read_acc_data(&self.file_path, index)
            .with_context(|| "delete elements error")?;
        backup_acc_data(&self.file_path, index)
            .with_context(|| "delete elements error")?;

        if num < data.values.len() {
            data.values = data.values[num..].to_vec();
            data.wits = generate_witness(&self.key.g, &self.key.n, &data.values);
            save_acc_data(&self.file_path, index, data.values.clone(), data.wits.clone())
                .with_context(|| "delete elements error")?;
            // Recompute the affected leaf's value.
            let leaf = &mut inner.accs.children[0].children[0];
            leaf.len -= num;
            let l = leaf.len;
            leaf.value = generate_acc(
                &self.key,
                &data.wits[l - 1],
                vec![data.values[l - 1].clone()],
            )
            .unwrap_or_default();
        } else {
            delete_acc_data(&self.file_path, index)
                .with_context(|| "delete elements error")?;
            // Remove the now-empty leaf and possibly its parent.
            inner.accs.children[0].children.remove(0);
            let new_len = inner.accs.children[0].children.len();
            inner.accs.children[0].len = new_len;
            if new_len == 0 && !inner.accs.children.is_empty() {
                inner.accs.children.remove(0);
                inner.accs.len = inner.accs.children.len();
            }
            if inner.accs.children.is_empty() {
                inner.curr_count = 0;
                inner.accs = AccNode {
                    value: self.key.g.to_bytes_be(),
                    ..Default::default()
                };
            }
        }
        inner.elem_nums = inner.elem_nums.saturating_sub(num);
        // Refresh siblings + root.
        if !inner.accs.children.is_empty() {
            let mut first = std::mem::take(&mut inner.accs.children[0]);
            self.update_acc(&mut first);
            inner.accs.children[0] = first;
            let mut root = std::mem::take(&mut inner.accs);
            self.update_acc(&mut root);
            inner.accs = root;
        }
        inner.deleted += num;
        Ok(())
    }

    /// Returns membership witness chains for the requested element indices.
    pub fn get_witness_chains(&self, indexs: &[i64]) -> Result<Vec<WitnessNode>> {
        let snap = self.get_snapshot();
        let mut data: Option<AccData> = None;
        let mut fidx: i64 = -1;
        let mut chains = Vec::with_capacity(indexs.len());
        for &idx in indexs {
            if idx <= snap.deleted as i64 || idx > (snap.deleted + snap.elem_nums) as i64 {
                bail!("bad index");
            }
            let group = (idx - 1) / DEFAULT_ELEMS_NUM as i64;
            if group > fidx {
                fidx = group;
                data = Some(read_acc_data(&self.file_path, fidx)?);
            }
            let d = data.as_ref().unwrap();
            let chain = build_witness_chain(&snap, idx, d)?;
            chains.push(chain);
        }
        Ok(chains)
    }

    /// Adds `elems` to the accumulator and produces an insertion proof.
    pub fn add_elements_and_proof(
        &self,
        elems: Vec<Vec<u8>>,
    ) -> Result<(WitnessNode, Vec<Vec<u8>>)> {
        let snapshot = self.get_snapshot();
        let mut exist = WitnessNode {
            elem: snapshot.accs.value.clone(),
            ..Default::default()
        };

        let start = std::time::Instant::now();
        while self.is_del.load(Ordering::Acquire) || !self.set_update(true) {
            if start.elapsed() > TIMEOUT {
                bail!("prove acc insertion proof: lock acquisition timed out");
            }
            thread::sleep(Duration::from_secs(1));
        }
        // Release on drop.
        let _guard = UpdateGuard(self);

        self.add_elements(elems)
            .with_context(|| "prove acc insertion proof")?;

        // Re-read state after update.
        let inner = self.inner.read();
        let mut count = 1usize;
        let mut p = &inner.accs;
        let mut q = &snapshot.accs;

        while count < DEFAULT_LEVEL {
            if p.children.is_empty() || q.children.is_empty() {
                break;
            }
            if p.len > q.len {
                // accumulator-grew path: the rest of the chain is `G`s
                for _ in count..DEFAULT_LEVEL {
                    let parent = WitnessNode {
                        acc: Some(Box::new(exist.clone())),
                        elem: self.key.g.to_bytes_be(),
                        wit: exist.elem.clone(),
                    };
                    exist = parent;
                }
                break;
            }
            count += 1;
            p = &p.children[p.children.len() - 1];
            q = &q.children[q.children.len() - 1];
            exist = WitnessNode {
                elem: q.value.clone(),
                wit: q.wit.clone(),
                acc: Some(Box::new(exist)),
            };
        }

        let mut p = &inner.accs;
        let mut accs = vec![Vec::new(); DEFAULT_LEVEL];
        for i in 0..DEFAULT_LEVEL {
            accs[DEFAULT_LEVEL - i - 1] = p.value.clone();
            if !p.children.is_empty() {
                p = &p.children[p.children.len() - 1];
            }
        }
        Ok((exist, accs))
    }

    /// Deletes `num` elements and produces a deletion proof.
    pub fn delete_elements_and_proof(
        &self,
        num: usize,
    ) -> Result<(WitnessNode, Vec<Vec<u8>>)> {
        {
            let inner = self.inner.read();
            if inner.elem_nums == 0 {
                bail!("prove acc deletion proof: delete null set");
            }
        }
        // Snapshot pre-delete witness chain.
        let exist = {
            let inner = self.inner.read();
            WitnessNode {
                elem: inner.accs.children[0].children[0].value.clone(),
                wit: inner.accs.children[0].children[0].wit.clone(),
                acc: Some(Box::new(WitnessNode {
                    elem: inner.accs.children[0].value.clone(),
                    wit: inner.accs.children[0].wit.clone(),
                    acc: Some(Box::new(WitnessNode {
                        elem: inner.accs.value.clone(),
                        ..Default::default()
                    })),
                })),
            }
        };

        let snapshot = self.get_snapshot();

        self.is_del.store(true, Ordering::Release);
        let start = std::time::Instant::now();
        while !self.set_update(true) {
            if start.elapsed() > TIMEOUT {
                self.is_del.store(false, Ordering::Release);
                bail!("prove acc deletion proof: lock acquisition timed out");
            }
            thread::sleep(Duration::from_secs(1));
        }
        self.is_del.store(false, Ordering::Release);
        let _guard = UpdateGuard(self);

        self.delete_elements(num)
            .with_context(|| "prove acc deletion proof")?;

        let inner = self.inner.read();
        let mut accs = vec![Vec::new(); DEFAULT_LEVEL];
        accs[DEFAULT_LEVEL - 1] = inner.accs.value.clone();
        let mut count = 1usize;
        let mut p = &inner.accs;
        let mut q = &snapshot.accs;
        while count < DEFAULT_LEVEL {
            if p.children.is_empty() || q.children.is_empty() {
                break;
            }
            if p.len < q.len {
                for i in (0..DEFAULT_LEVEL - count - 1).rev() {
                    accs[i] = self.key.g.to_bytes_be();
                }
                break;
            }
            count += 1;
            p = &p.children[0];
            q = &q.children[0];
            accs[DEFAULT_LEVEL - count] = p.value.clone();
        }
        Ok((exist, accs))
    }

    /// Rebuilds the in-memory accumulator state from on-disk sub-acc files.
    fn construct_muti_acc(&self, rear: i64) -> Result<()> {
        let mut inner = self.inner.write();
        if rear == inner.deleted as i64 {
            return Ok(());
        }
        let num = ((rear - inner.deleted as i64 - 1) / DEFAULT_ELEMS_NUM as i64) as i64;
        let offset = inner.deleted % DEFAULT_ELEMS_NUM;
        for i in 0..=num {
            let index = (inner.deleted as i64 / DEFAULT_ELEMS_NUM as i64) + i;
            let mut backup_or = read_backup(&self.file_path, index).ok();
            let need_active = match &backup_or {
                Some(b) => b.values.len() + offset != DEFAULT_ELEMS_NUM,
                None => true,
            };
            let mut data = if need_active {
                read_acc_data(&self.file_path, index)?
            } else {
                recovery_acc_data(&self.file_path, index)?;
                backup_or.take().unwrap()
            };

            let right = data.values.len();
            if i == 0 && DEFAULT_ELEMS_NUM - offset < right {
                let left = inner.deleted % DEFAULT_ELEMS_NUM - (DEFAULT_ELEMS_NUM - right);
                data.values = data.values[left..right].to_vec();
                data.wits = generate_witness(&self.key.g, &self.key.n, &data.values);
                save_acc_data(
                    &self.file_path,
                    index,
                    data.values.clone(),
                    data.wits.clone(),
                )?;
            }
            let len = data.values.len();
            let mut node = AccNode {
                len,
                value: generate_acc(
                    &self.key,
                    &data.wits[len - 1],
                    vec![data.values[len - 1].clone()],
                )
                .unwrap_or_default(),
                ..Default::default()
            };
            // Adopt the sub-accumulator value as the leaf's `value`.
            let _ = std::mem::take(&mut node.children);
            self.add_sub_acc_by_batch(&mut inner, node);
            if i == 0 && offset > 0 {
                inner.curr_count += offset;
            }
        }

        // Update accumulator values + witnesses across all parents and the root.
        let parent_count = inner.accs.children.len();
        for i in 0..parent_count {
            let mut p = std::mem::take(&mut inner.accs.children[i]);
            self.update_acc(&mut p);
            inner.accs.children[i] = p;
        }
        let mut root = std::mem::take(&mut inner.accs);
        self.update_acc(&mut root);
        inner.accs = root;

        Ok(())
    }
}

/// RAII guard releasing the update flag when dropped.
struct UpdateGuard<'a>(&'a MutiLevelAcc);
impl Drop for UpdateGuard<'_> {
    fn drop(&mut self) {
        self.0.set_update(false);
    }
}

// ---------------------------------------------------------------------------
// Witness chain construction
// ---------------------------------------------------------------------------

fn build_witness_chain(snap: &AccSnapshot, mut index: i64, data: &AccData) -> Result<WitnessNode> {
    let idx_in_file =
        ((index - (DEFAULT_ELEMS_NUM as i64 - data.values.len() as i64) - 1) % DEFAULT_ELEMS_NUM as i64)
            as usize;
    index -= (snap.deleted - snap.deleted % DEFAULT_ELEMS_NUM) as i64;

    let mut p = &snap.accs;
    let mut wit: Option<WitnessNode> = None;
    let mut i = 0usize;
    while i < DEFAULT_LEVEL {
        wit = Some(WitnessNode {
            elem: p.value.clone(),
            wit: p.wit.clone(),
            acc: wit.map(Box::new),
        });
        let size = (DEFAULT_ELEMS_NUM as i64).pow((DEFAULT_LEVEL - i - 1) as u32);
        let mut child_idx = (index - 1) / size;
        child_idx %= size;
        if (p.children.len() as i64) < child_idx + 1 || p.children.is_empty() {
            i += 1;
            continue;
        }
        p = &p.children[child_idx as usize];
        i += 1;
    }
    if i < DEFAULT_LEVEL {
        return Err(anyhow!("get witness node error"));
    }
    let chain = WitnessNode {
        elem: data.values[idx_in_file].clone(),
        wit: data.wits[idx_in_file].clone(),
        acc: wit.map(Box::new),
    };
    Ok(chain)
}

// ---------------------------------------------------------------------------
// Verification functions (verifier-side)
// ---------------------------------------------------------------------------

/// Verifies a single accumulator membership proof.
fn verify_acc(key: &RsaKey, acc: &[u8], u: &[u8], wit: &[u8]) -> bool {
    let e = h_prime(&BigUint::from_bytes_be(u));
    let dash = BigUint::from_bytes_be(wit).modpow(&e, &key.n);
    dash == BigUint::from_bytes_be(acc)
}

/// Verifies a complete multi-level accumulator witness chain.
pub fn verify_mutilevel_acc(key: &RsaKey, wits: Option<&mut WitnessNode>, acc: &[u8]) -> bool {
    let mut current_wit = match wits {
        Some(w) => w,
        None => return false,
    };
    while let Some(acc_node) = &mut current_wit.acc {
        if !verify_acc(key, &acc_node.elem, &current_wit.elem, &current_wit.wit) {
            return false;
        }
        current_wit = acc_node;
    }
    current_wit.elem.eq(acc)
}

/// Verifies an insertion update for a multi-level accumulator.
pub fn verify_insert_update(
    key: RsaKey,
    exist: Option<Box<WitnessNode>>,
    elems: Vec<Vec<u8>>,
    accs: Vec<Vec<u8>>,
    acc: Vec<u8>,
) -> bool {
    if exist.is_none() || elems.is_empty() || accs.len() < DEFAULT_LEVEL {
        return false;
    }
    let mut p = exist.clone().unwrap().as_ref().clone();
    while p.acc.is_some() && p.acc.as_ref().unwrap().elem == p.wit {
        p = p.acc.unwrap().as_ref().clone();
    }
    if !verify_mutilevel_acc(&key, Some(&mut p.clone()), &acc) {
        return false;
    }

    let sub_acc = generate_acc(&key, &exist.as_ref().unwrap().elem, elems);
    if !sub_acc.eq(&Some(accs[0].clone())) {
        return false;
    }

    let mut count = 1usize;
    let mut p = *exist.unwrap();
    while p.acc.is_some() {
        let sub_acc = generate_acc(&key, &p.wit, vec![accs[count - 1].clone()]);
        if !sub_acc.eq(&Some(accs[count].clone())) {
            return false;
        }
        p = *p.acc.unwrap();
        count += 1;
    }
    true
}

/// Performs batched verification of multi-level accumulator witnesses.
pub fn verify_mutilevel_acc_for_batch(
    key: &RsaKey,
    base_idx: i64,
    wits: Vec<WitnessNode>,
    acc: &[u8],
) -> bool {
    let mut sub_acc: Option<Vec<u8>> = None;
    let default_elems_num = DEFAULT_ELEMS_NUM as i64;
    for (i, witness) in wits.iter().enumerate() {
        if let Some(sa) = &sub_acc {
            let parent_elem = witness.acc.as_ref().map(|b| b.elem.clone()).unwrap_or_default();
            if parent_elem != *sa {
                return false;
            }
        }
        if (i as i64 + base_idx) % default_elems_num == 0 || i == wits.len() - 1 {
            if !verify_mutilevel_acc(key, Some(&mut witness.clone()), acc) {
                return false;
            }
            sub_acc = None;
            continue;
        }
        let mut rng = rand::thread_rng();
        if rng.gen_range(0..100) < 20
            && !verify_acc(
                key,
                &witness.acc.as_ref().unwrap().elem,
                &witness.elem,
                &witness.wit,
            )
        {
            return false;
        }
        sub_acc = witness.acc.as_ref().map(|b| b.elem.clone());
    }
    true
}

/// Verifies a deletion update for a multi-level accumulator.
pub fn verify_delete_update(
    key: RsaKey,
    exist: &mut WitnessNode,
    elems: Vec<Vec<u8>>,
    accs: Vec<Vec<u8>>,
    acc: &[u8],
) -> bool {
    if elems.is_empty() || accs.len() < DEFAULT_LEVEL {
        return false;
    }
    if !verify_mutilevel_acc(&key, Some(exist), acc) {
        return false;
    }
    let mut sub_acc = generate_acc(&key, &accs[0], elems);
    if !sub_acc.eq(&Some(exist.elem.clone())) {
        return false;
    }
    let mut p = exist;
    let mut count = 1usize;
    while p.acc.is_some() {
        if accs[count - 1].eq(&key.g.to_bytes_be()) {
            sub_acc = Some(p.wit.clone());
        } else {
            sub_acc = generate_acc(&key, &p.wit, vec![accs[count - 1].clone()]);
        }
        if !sub_acc.eq(&Some(accs[count].clone())) {
            return false;
        }
        p = p.acc.as_mut().unwrap();
        count += 1;
    }
    true
}

// ---------------------------------------------------------------------------
// (re-exports)
// ---------------------------------------------------------------------------

// Convenience helpers expected by Path-based callers.
pub use super::file_manage::DEFAULT_ELEMS_NUM as ELEMS_PER_SUB_ACC;
#[allow(unused_imports)]
pub(crate) use std::path::PathBuf;
// Silence unused import warning if `Path` is only referenced in docs.
#[allow(dead_code)]
fn _link_path(_p: &Path) {}
