//! # Prover State Machine
//!
//! Port of `pois/prove.go` from the Go reference.  Wraps a stateful
//! prover that:
//! - generates idle file sets on disk
//! - produces commit, accumulator, space and deletion proofs
//! - tracks `front` / `rear` / `space` budgets
//!
//! All globals from the Go side (`FileSize`, `AccPath`, ...) live on
//! the [`Prover`] instance so that multiple provers can coexist within
//! a single process.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use crossbeam_channel::{bounded, Receiver, Sender};
use parking_lot::{Mutex, RwLock};
use rayon::prelude::*;

use crate::acc::file_manage::{
    backup_acc_data_for_chall, clean_backup, delete_acc_data, DEFAULT_ELEMS_NUM,
};
use crate::acc::multi_level_acc::{MutiLevelAcc, WitnessNode};
use crate::acc::RsaKey;
use crate::expanders::generate_expanders::{calc_parents, construct_stacked_expanders};
use crate::expanders::generate_idle_file::{
    get_hash, AUX_FILE, CLUSTER_DIR_NAME, COMMIT_FILE, DEFAULT_AUX_SIZE, DEFAULT_IDLE_FILES_PATH,
    FILE_NAME, HASH_SIZE, SET_DIR_NAME,
};
use crate::expanders::{get_bytes, Expanders, Node, NodeType};
use crate::tree::{
    calc_light_mht_with_aux, calc_light_mht_with_bytes, get_path_proof, get_path_proof_with_aux,
    get_root, init_mht_pool, DEFAULT_HASH_SIZE,
};
use crate::util::{
    copy_files, delete_dir, delete_file, read_file_to_buf, read_proof_file,
};

use super::prove::{AccProof, CommitProof, Commits, DeletionProof, MhtProof, SpaceProof};

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

pub const DEFAULT_CHAL_GROUP: i64 = 4;
pub const DEFAULT_CHAL_GROUP_NUM: i64 = 256;
pub const DEFAULT_ACC_PATH: &str = "./acc/";
pub const DEFAULT_CHALL_ACC_PATH: &str = "./chall_acc/";
pub const DEFAULT_MAX_PROOF_THREAD: usize = 4;
pub const MINI_FILE_SIZE: i64 = 1024 * 1024;

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default)]
pub struct Config {
    pub acc_path: String,
    pub chall_acc_path: String,
    pub idle_file_path: String,
    pub max_proof_thread: usize,
}

#[derive(Clone, Debug)]
pub struct ResolvedConfig {
    pub acc_path: String,
    pub chall_acc_path: String,
    pub idle_file_path: String,
    pub max_proof_thread: usize,
    pub file_size: i64, // in megabytes; matches Go FileSize semantics
}

impl ResolvedConfig {
    fn resolve(cfg: Config, expanders: &Expanders) -> Result<Self> {
        let acc_path = if cfg.acc_path.is_empty() {
            DEFAULT_ACC_PATH.to_string()
        } else {
            cfg.acc_path
        };
        let mut chall_acc_path = if cfg.chall_acc_path.is_empty() {
            DEFAULT_CHALL_ACC_PATH.to_string()
        } else {
            cfg.chall_acc_path
        };
        if chall_acc_path == acc_path {
            chall_acc_path = DEFAULT_CHALL_ACC_PATH.to_string();
        }
        let idle_file_path = if cfg.idle_file_path.is_empty() {
            DEFAULT_IDLE_FILES_PATH.to_string()
        } else {
            cfg.idle_file_path
        };
        let max_proof_thread = if cfg.max_proof_thread == 0 {
            DEFAULT_MAX_PROOF_THREAD
        } else {
            cfg.max_proof_thread
        };
        if !Path::new(&idle_file_path).exists() {
            std::fs::create_dir_all(&idle_file_path)
                .with_context(|| "ensure idle file path exists")?;
        }
        let file_size = HASH_SIZE as i64 * expanders.n / (1024 * 1024);
        Ok(ResolvedConfig {
            acc_path,
            chall_acc_path,
            idle_file_path,
            max_proof_thread,
            file_size,
        })
    }
}

// ---------------------------------------------------------------------------
// ChainState
// ---------------------------------------------------------------------------

pub struct ChainState {
    pub acc: Option<Arc<MutiLevelAcc>>,
    pub challenging: bool,
    pub del_ch: Option<(Sender<()>, Receiver<()>)>,
    pub rear: i64,
    pub front: i64,
}

impl Default for ChainState {
    fn default() -> Self {
        ChainState {
            acc: None,
            challenging: false,
            del_ch: None,
            rear: 0,
            front: 0,
        }
    }
}

#[derive(Clone)]
pub struct ChainStateSnapshot {
    pub acc: Option<Arc<MutiLevelAcc>>,
    pub rear: i64,
    pub front: i64,
}

impl std::fmt::Debug for ChainStateSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChainStateSnapshot")
            .field("acc_present", &self.acc.is_some())
            .field("rear", &self.rear)
            .field("front", &self.front)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

#[derive(Default, Debug)]
struct Ctx {
    commited: AtomicI64,
    added: AtomicI64,
    generated: AtomicI64,
    proofed: AtomicI64,
}

pub struct Prover {
    pub expanders: Expanders,
    pub id: Vec<u8>,
    #[doc(hidden)]
    pub state: RwLock<ProverState>,

    delete: AtomicBool,
    update: AtomicBool,
    sync: AtomicBool,
    generate: AtomicBool,

    ctx: Ctx,
    chain_state: Mutex<ChainState>,

    pub acc_manager: RwLock<Option<Arc<MutiLevelAcc>>>,
    pub config: RwLock<Option<ResolvedConfig>>,
}

#[derive(Debug, Default, Clone)]
pub struct ProverState {
    pub rear: i64,
    pub front: i64,
    pub space: i64,
    pub set_len: i64,
    pub cluster_size: i64,
}

impl Prover {
    /// Creates a fresh Prover instance.
    pub fn new(k: i64, n: i64, d: i64, id: Vec<u8>, space: i64, set_len: i64) -> Result<Arc<Self>> {
        if k <= 0 || n <= 0 || d <= 0 || space <= 0 || id.is_empty() {
            bail!("bad params");
        }
        let expanders = construct_stacked_expanders(k, n, d);
        init_mht_pool(n as usize);
        let prover = Prover {
            expanders,
            id,
            state: RwLock::new(ProverState {
                space,
                set_len,
                cluster_size: k,
                ..Default::default()
            }),
            delete: AtomicBool::new(false),
            update: AtomicBool::new(false),
            sync: AtomicBool::new(false),
            generate: AtomicBool::new(false),
            ctx: Ctx::default(),
            chain_state: Mutex::new(ChainState::default()),
            acc_manager: RwLock::new(None),
            config: RwLock::new(None),
        };
        Ok(Arc::new(prover))
    }

    pub fn get_front(&self) -> i64 {
        self.state.read().front
    }
    pub fn get_rear(&self) -> i64 {
        self.state.read().rear
    }
    pub fn get_space(&self) -> i64 {
        self.state.read().space
    }
    pub fn get_num_of_file_in_set(&self) -> i64 {
        let s = self.state.read();
        s.set_len * s.cluster_size
    }

    pub fn return_space(&self, size: i64) {
        let mut s = self.state.write();
        s.space += size;
    }

    pub fn get_acc_value(&self) -> Vec<u8> {
        let key_len = 256usize;
        let mgr = self
            .acc_manager
            .read()
            .clone()
            .expect("acc manager not initialised");
        let snap = mgr.get_snapshot();
        let acc = snap.accs.value;
        if acc.len() > key_len {
            return acc[acc.len() - key_len..].to_vec();
        }
        let mut res = vec![0u8; key_len];
        res[key_len - acc.len()..].copy_from_slice(&acc);
        res
    }

    pub fn commit_data_is_ready(&self) -> bool {
        let commited = self.ctx.commited.load(Ordering::Acquire);
        let generated = self.ctx.generated.load(Ordering::Acquire);
        let need = self.get_num_of_file_in_set();
        generated - commited >= need
    }

    pub fn get_chain_state(&self) -> ChainStateSnapshot {
        let cs = self.chain_state.lock();
        ChainStateSnapshot {
            acc: cs.acc.clone(),
            rear: cs.rear,
            front: cs.front,
        }
    }

    pub fn rest_challenge_state(&self) -> Result<()> {
        let mut cs = self.chain_state.lock();
        self.ctx.proofed.store(0, Ordering::Release);
        cs.del_ch = None;
        cs.challenging = false;
        let cfg = self.config.read();
        if cs.front >= DEFAULT_ELEMS_NUM as i64 {
            let index = (cs.front - DEFAULT_ELEMS_NUM as i64) / DEFAULT_ELEMS_NUM as i64;
            if let Some(c) = cfg.as_ref() {
                let _ = delete_acc_data(&c.chall_acc_path, index);
            }
        }
        Ok(())
    }

    pub fn set_challenge_state_for_test(&self, front: i64, rear: i64) {
        let mut cs = self.chain_state.lock();
        *cs = ChainState {
            rear,
            front,
            ..Default::default()
        };
    }

    /// Initialises the accumulator and challenge-accumulator stores.
    pub fn init(self: &Arc<Self>, key: RsaKey, config: Config) -> Result<()> {
        if key.g.bits() == 0 || key.n.bits() == 0 {
            bail!("bad init params");
        }
        let resolved = ResolvedConfig::resolve(config, &self.expanders)?;
        let acc_mgr = MutiLevelAcc::new(&resolved.acc_path, key.clone())
            .with_context(|| "init prover error")?;
        let _ = MutiLevelAcc::new(&resolved.chall_acc_path, key)
            .with_context(|| "init prover error")?;
        *self.acc_manager.write() = Some(acc_mgr);
        *self.config.write() = Some(resolved);
        Ok(())
    }

    /// Recovers prover state from disk (acc files + idle file directory).
    pub fn recovery(
        self: &Arc<Self>,
        key: RsaKey,
        front: i64,
        rear: i64,
        config: Config,
    ) -> Result<()> {
        let s = self.state.read();
        if key.g.bits() == 0
            || key.n.bits() == 0
            || front < 0
            || rear < 0
            || front > rear
            || rear % (s.set_len * s.cluster_size) != 0
        {
            bail!("bad recovery params");
        }
        drop(s);

        let resolved = ResolvedConfig::resolve(config, &self.expanders)?;

        let acc_mgr = MutiLevelAcc::recovery(&resolved.acc_path, key, front, rear)
            .with_context(|| "recovery prover error")?;

        // recover context counters
        let generated = self.calc_generated_file(&resolved.idle_file_path)?;
        let s_clone = self.state.read().clone();
        let set_size = s_clone.set_len * s_clone.cluster_size;
        let generated = if generated % set_size != 0 {
            generated - generated % set_size
        } else {
            generated
        };
        let file_size = resolved.file_size;

        {
            let mut s = self.state.write();
            s.front = front;
            s.rear = rear;
            self.ctx.generated.store(rear + generated, Ordering::Release);
            self.ctx.added.store(rear + generated, Ordering::Release);
            self.ctx.commited.store(rear, Ordering::Release);
            s.space -= (s.rear - s.front) * file_size;
            s.space -= generated / s.cluster_size * (s.cluster_size + self.expanders.k) * file_size;
        }

        // mirror acc data to challenge path
        copy_files(&resolved.acc_path, &resolved.chall_acc_path)
            .with_context(|| "recovery prover error")?;

        *self.acc_manager.write() = Some(acc_mgr);
        *self.config.write() = Some(resolved);

        self.cleanup_disk()?;
        Ok(())
    }

    /// Removes stale files from previous runs.
    pub fn cleanup_disk(self: &Arc<Self>) -> Result<()> {
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .idle_file_path
            .clone();

        let (front, rear, set_size) = {
            let s = self.state.read();
            (s.front, s.rear, s.set_len * s.cluster_size)
        };

        if front == rear && front == 0 {
            let _ = delete_dir(&cfg);
            std::fs::create_dir_all(&cfg).ok();
        }

        if front > 0 {
            let _ = self.delete_files();
        }

        let num = set_size;
        if num <= 0 {
            return Ok(());
        }
        let mut i = ((front + num - 1) / num) * num;
        while i < rear - num {
            let _ = self.organize_files(i, num);
            i += num;
        }
        Ok(())
    }

    /// Generates a single idle file set on disk.
    ///
    /// **Not thread-safe** — concurrent invocations will be rejected.
    pub fn generate_idle_file_set(self: &Arc<Self>) -> Result<()> {
        let (set_len, cluster_size, file_size, idle_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.set_len, s.cluster_size, cfg.3, cfg.2)
        };
        let file_num = set_len * cluster_size;
        {
            let s = self.state.read();
            if s.space < (file_num + set_len * self.expanders.k) * file_size {
                bail!("generate idle file set error: not enough space");
            }
        }
        if self
            .generate
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            bail!("generate idle file set error: lock is occupied");
        }
        let _g = AutoFlag::new(&self.generate);

        let start = {
            let mut s = self.state.write();
            self.ctx.added.fetch_add(file_num, Ordering::AcqRel);
            s.space -= (file_num + set_len * self.expanders.k) * file_size;
            (self.ctx.added.load(Ordering::Acquire) - file_num) / s.cluster_size + 1
        };

        if let Err(err) = self.expanders.generate_idle_file_set(
            &self.id, start, set_len, &idle_path,
        ) {
            let mut s = self.state.write();
            self.ctx.added.fetch_sub(file_num, Ordering::AcqRel);
            s.space += (file_num + set_len * self.expanders.k) * file_size;
            return Err(err).with_context(|| "generate idle file set error");
        }

        self.ctx.generated.fetch_add(file_num, Ordering::AcqRel);
        Ok(())
    }

    /// Generates `t_num` idle file sets in parallel.
    pub fn generate_idle_file_sets(self: &Arc<Self>, t_num: usize) -> Result<()> {
        if t_num == 0 {
            bail!("generate idle file sets error: bad thread number");
        }
        let (set_len, cluster_size, file_size, idle_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.set_len, s.cluster_size, cfg.3, cfg.2)
        };
        let file_num = set_len * cluster_size;
        let mut t_num = t_num;
        {
            let s = self.state.read();
            if s.space < (file_num + set_len * self.expanders.k) * file_size * t_num as i64 {
                if s.space >= (file_num + set_len * self.expanders.k) * file_size {
                    t_num = 1;
                } else {
                    bail!("generate idle file sets error: not enough space");
                }
            }
        }

        if self
            .generate
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            bail!("generate idle file sets error: lock is occupied");
        }
        let _g = AutoFlag::new(&self.generate);

        let curr_index = self.ctx.added.load(Ordering::Acquire) / cluster_size + 1;
        self.ctx
            .added
            .fetch_add(file_num * t_num as i64, Ordering::AcqRel);
        {
            let mut s = self.state.write();
            s.space -= (file_num + set_len * self.expanders.k) * file_size * t_num as i64;
        }

        let starts: Vec<i64> = (0..t_num as i64)
            .map(|i| curr_index + i * set_len)
            .collect();
        let id = self.id.clone();
        let exp = self.expanders.clone();
        let results: Vec<Result<()>> = starts
            .into_par_iter()
            .map(|start| {
                exp.generate_idle_file_set(&id, start, set_len, &idle_path)
            })
            .collect();
        let err = results.into_iter().find_map(|r| r.err());
        if let Some(e) = err {
            self.ctx
                .added
                .fetch_sub(file_num * t_num as i64, Ordering::AcqRel);
            let mut s = self.state.write();
            s.space += (file_num + set_len * self.expanders.k) * file_size * t_num as i64;
            return Err(e.context("generate idle file sets error"));
        }
        self.ctx
            .generated
            .fetch_add(file_num * t_num as i64, Ordering::AcqRel);
        Ok(())
    }

    /// Rolls the commit pointer back after a failed verifier handshake.
    pub fn commit_rollback(self: &Arc<Self>) -> bool {
        if self
            .update
            .compare_exchange(true, false, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let s = self.state.read();
            self.ctx
                .commited
                .fetch_sub(s.set_len * s.cluster_size, Ordering::AcqRel);
            true
        } else {
            false
        }
    }

    /// Rolls the accumulator back after a failed update.
    pub fn acc_rollback(self: &Arc<Self>, is_del: bool) -> bool {
        if is_del {
            if self
                .delete
                .compare_exchange(true, false, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return false;
            }
        } else {
            if self
                .update
                .compare_exchange(true, false, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return false;
            }
            let s = self.state.read();
            self.ctx
                .commited
                .fetch_sub(s.set_len * s.cluster_size, Ordering::AcqRel);
        }
        let mgr = self.acc_manager.read().clone();
        match mgr {
            Some(m) => m.rollback(),
            None => false,
        }
    }

    /// Syncs prover state to match the chain-side `(front, rear)`.
    pub fn sync_chain_pois_status(self: &Arc<Self>, front: i64, rear: i64) -> Result<()> {
        {
            let s = self.state.read();
            if s.front == front && s.rear == rear {
                return Ok(());
            }
        }
        self.sync.store(true, Ordering::Release);
        struct G<'a>(&'a AtomicBool);
        impl Drop for G<'_> {
            fn drop(&mut self) {
                self.0.store(false, Ordering::Release);
            }
        }
        let _g = G(&self.sync);

        while !self.update.load(Ordering::Acquire) && !self.delete.load(Ordering::Acquire) {
            std::thread::yield_now();
        }
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        let key = {
            let mgr = self.acc_manager.read().clone().unwrap();
            mgr.key.clone()
        };
        let new_mgr = MutiLevelAcc::recovery(&cfg.0, key, front, rear)
            .with_context(|| "reflash acc error")?;
        *self.acc_manager.write() = Some(new_mgr);
        let mut s = self.state.write();
        s.front = front;
        s.rear = rear;
        self.ctx.commited.store(rear, Ordering::Release);
        Ok(())
    }

    /// Updates prover counters after a successful commit/delete verification.
    pub fn update_status(self: &Arc<Self>, num: i64, is_delete: bool) -> Result<()> {
        if num < 0 {
            bail!("update prover status error: bad files number");
        }
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        if is_delete {
            if self
                .delete
                .compare_exchange(true, false, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                bail!("update prover status error: no delete task pending update");
            }
            let mut s = self.state.write();
            s.front += num;
            let mgr = self.acc_manager.read().clone().unwrap();
            mgr.update_snapshot();
            drop(s);
            clean_backup(
                &cfg.0,
                (self.state.read().front - 1) / DEFAULT_ELEMS_NUM as i64,
            )?;
            return Ok(());
        }

        if self
            .update
            .compare_exchange(true, false, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            bail!("update prover status error: no update task pending update");
        }
        {
            let mut s = self.state.write();
            s.rear += num;
            let mgr = self.acc_manager.read().clone().unwrap();
            mgr.update_snapshot();
        }
        let s = self.state.read().clone();
        if let Err(e) = self.organize_files(s.rear - num, num) {
            return Err(e).with_context(|| "update prover status error");
        }
        let mut i = ((s.front + num - 1) / num) * num;
        while i < s.rear - num {
            let _ = self.organize_files(i, num);
            i += num;
        }
        Ok(())
    }

    /// Sets up the challenge state for proving.
    pub fn set_challenge_state(
        self: &Arc<Self>,
        key: RsaKey,
        acc_snp: Vec<u8>,
        front: i64,
        rear: i64,
    ) -> Result<()> {
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        let chain_acc = num_bigint_dig::BigUint::from_bytes_be(&acc_snp);
        let chall_acc = MutiLevelAcc::recovery(&cfg.1, key, front, rear)
            .with_context(|| "recovery chain state error")?;
        let snap = chall_acc.get_snapshot();
        let local = num_bigint_dig::BigUint::from_bytes_be(&snap.accs.value);
        if chain_acc != local {
            bail!("recovery chain state error: the restored acc value is not equal to the snapshot value");
        }
        let (s, r) = bounded(1);
        let mut cs = self.chain_state.lock();
        *cs = ChainState {
            acc: Some(chall_acc),
            challenging: true,
            del_ch: Some((s, r)),
            rear,
            front,
        };
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Commits & Proofs
    // -----------------------------------------------------------------------

    /// Returns a fresh batch of commit data for the verifier.
    pub fn get_idle_file_set_commits(self: &Arc<Self>) -> Result<Commits> {
        if self.sync.load(Ordering::Acquire) {
            bail!("get commits error: syncing status, please try again");
        }
        if self
            .update
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            bail!("get commits error: lock is occupied");
        }

        let (set_len, cluster_size, idle_file_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.set_len, s.cluster_size, cfg.2.clone())
        };
        let commited = self.ctx.commited.load(Ordering::Acquire);
        let generated = self.ctx.generated.load(Ordering::Acquire);
        let commit_num = set_len * cluster_size;
        if generated - commited < commit_num {
            self.update.store(false, Ordering::Release);
            bail!("get commits error: bad commit data");
        }

        let set_idx = commited / (set_len * cluster_size) + 1;
        let name = Path::new(&idle_file_path)
            .join(format!("{}-{}", SET_DIR_NAME, set_idx))
            .join(COMMIT_FILE);
        let root_num = (commit_num + self.expanders.k * set_len + 1) as usize;
        let roots = match read_proof_file(&name, root_num, DEFAULT_HASH_SIZE) {
            Ok(v) => v,
            Err(e) => {
                self.update.store(false, Ordering::Release);
                return Err(e).with_context(|| "get commits error");
            }
        };
        let mut commits = Commits {
            roots,
            file_indexs: Vec::with_capacity(commit_num as usize),
        };
        for i in 0..commit_num {
            commits.file_indexs.push(commited + i + 1);
        }
        self.ctx.commited.fetch_add(commit_num, Ordering::AcqRel);
        Ok(commits)
    }

    /// Generates both commit and accumulator proofs for the supplied challenges.
    pub fn prove_commit_and_acc(
        self: &Arc<Self>,
        challenges: Vec<Vec<i64>>,
    ) -> Result<Option<(Vec<Vec<CommitProof>>, AccProof)>> {
        if !self.update.load(Ordering::Acquire) {
            return Ok(None);
        }
        let commit_proofs = self.prove_commits(&challenges)?;
        let acc_proof = self.prove_acc(&challenges)?;
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        let rear = self.state.read().rear;
        let index = rear / DEFAULT_ELEMS_NUM as i64;
        backup_acc_data_for_chall(&cfg.0, &cfg.1, index)?;
        Ok(Some((commit_proofs, acc_proof)))
    }

    fn prove_acc(self: &Arc<Self>, challenges: &[Vec<i64>]) -> Result<AccProof> {
        let (set_len, cluster_size, idle_file_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.set_len, s.cluster_size, cfg.2)
        };
        if challenges.len() as i64 != set_len {
            bail!("update acc error: bad challenges data");
        }
        let file_num = set_len * cluster_size;
        let mut labels: Vec<Vec<u8>> = vec![Vec::new(); file_num as usize];
        let mut indexs: Vec<i64> = vec![0; file_num as usize];

        let set_idx = (challenges[0][0] - 1) / set_len + 1;
        let fname = Path::new(&idle_file_path)
            .join(format!("{}-{}", SET_DIR_NAME, set_idx))
            .join(COMMIT_FILE);
        let roots = read_proof_file(
            &fname,
            ((self.expanders.k + cluster_size) * set_len + 1) as usize,
            DEFAULT_HASH_SIZE,
        )?;
        for i in 0..set_len {
            for j in 0..cluster_size {
                let index = (challenges[i as usize][0] - 1) * cluster_size + j + 1;
                indexs[(i * cluster_size + j) as usize] = index;
                let root = &roots[((self.expanders.k + j) * set_len + i) as usize];
                let mut label = Vec::with_capacity(self.id.len() + 8 + root.len());
                label.extend_from_slice(&self.id);
                label.extend_from_slice(&get_bytes(index));
                label.extend_from_slice(root);
                labels[(i * cluster_size + j) as usize] = get_hash(&label);
            }
        }

        let mgr = self
            .acc_manager
            .read()
            .clone()
            .ok_or_else(|| anyhow!("acc manager not initialised"))?;
        let (wit_chain, acc_path) = mgr.add_elements_and_proof(labels.clone())?;
        Ok(AccProof {
            indexs,
            labels,
            wit_chains: Some(Box::new(wit_chain)),
            acc_path,
        })
    }

    /// Reads one file's labels into `buf`.
    pub fn read_file_labels(&self, cluster: i64, fidx: i64, buf: &mut [u8]) -> Result<()> {
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        let s = self.state.read();
        let name = Path::new(&cfg.2)
            .join(format!("{}-{}", SET_DIR_NAME, (cluster - 1) / s.set_len + 1))
            .join(format!("{}-{}", CLUSTER_DIR_NAME, cluster))
            .join(format!("{}-{}", FILE_NAME, fidx + self.expanders.k));
        read_file_to_buf(&name, buf).with_context(|| "read file labels error")
    }

    /// Reads a file's aux Merkle tree slice into `buf`.
    pub fn read_aux_data(&self, cluster: i64, fidx: i64, buf: &mut [u8]) -> Result<()> {
        let cfg = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .clone_basic();
        let s = self.state.read();
        let name = Path::new(&cfg.2)
            .join(format!("{}-{}", SET_DIR_NAME, (cluster - 1) / s.set_len + 1))
            .join(format!("{}-{}", CLUSTER_DIR_NAME, cluster))
            .join(format!("{}-{}", AUX_FILE, fidx + self.expanders.k));
        read_file_to_buf(&name, buf).with_context(|| "read aux data error")
    }

    fn prove_commits(self: &Arc<Self>, challenges: &[Vec<i64>]) -> Result<Vec<Vec<CommitProof>>> {
        let (set_len, cluster_size, idle_file_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.set_len, s.cluster_size, cfg.2)
        };
        let lens = challenges.len();
        let mut proof_set: Vec<Vec<CommitProof>> = vec![Vec::new(); lens];
        for i in 0..lens {
            let mut proofs: Vec<CommitProof> = Vec::with_capacity(challenges[i].len() - 1);
            for _ in 0..challenges[i].len() - 1 {
                proofs.push(CommitProof::default_empty());
            }
            let fdir = PathBuf::from(&idle_file_path)
                .join(format!("{}-{}", SET_DIR_NAME, (challenges[i][0] - 1) / set_len + 1))
                .join(format!("{}-{}", CLUSTER_DIR_NAME, challenges[i][0]));
            for j in 1..=proofs.len() as i64 {
                let mut index = challenges[i][j as usize];
                if j > cluster_size + 1 {
                    index = proofs[(j - 2) as usize].parents
                        [challenges[i][j as usize] as usize]
                        .index as i64;
                }
                let layer = if j < cluster_size + 1 {
                    self.expanders.k + j - 1
                } else {
                    index / self.expanders.n
                };
                let mut neighbor: Option<PathBuf> = None;
                if layer != 0 || i != 0 {
                    let mut cid = challenges[i][0] - 1;
                    if cid % set_len == 0 {
                        cid += set_len;
                    }
                    neighbor = Some(
                        PathBuf::from(&idle_file_path)
                            .join(format!("{}-{}", SET_DIR_NAME, (challenges[i][0] - 1) / set_len + 1))
                            .join(format!("{}-{}", CLUSTER_DIR_NAME, cid))
                            .join(format!(
                                "{}-{}",
                                FILE_NAME,
                                layer - (set_len - i as i64) / set_len
                            )),
                    );
                }
                proofs[(j - 1) as usize] = self.generate_commit_proof(
                    &fdir,
                    neighbor.as_deref(),
                    challenges[i][0],
                    index,
                    layer,
                )?;
            }
            proof_set[i] = proofs;
        }
        Ok(proof_set)
    }

    fn generate_path_proof(
        &self,
        mht: &mut crate::tree::LightMHT,
        data: &[u8],
        index: i64,
        node_idx: i64,
    ) -> Result<MhtProof> {
        let hash_size = HASH_SIZE as usize;
        calc_light_mht_with_bytes(mht, data, hash_size);
        let path = get_path_proof(mht, data, index as usize, hash_size)
            .with_context(|| "generate path proof error")?;
        let label = data[index as usize * hash_size..(index as usize + 1) * hash_size].to_vec();
        Ok(MhtProof {
            index: node_idx as NodeType,
            label,
            paths: path.path,
            locs: path.locs,
        })
    }

    fn get_path_proof_with_aux(
        &self,
        aux: &[u8],
        data: &[u8],
        index: i64,
        node_idx: i64,
    ) -> Result<MhtProof> {
        let hash_size = HASH_SIZE as usize;
        let path = get_path_proof_with_aux(data, aux, index as usize, hash_size)
            .with_context(|| "get path proof with aux error")?;
        let label = data[index as usize * hash_size..(index as usize + 1) * hash_size].to_vec();
        Ok(MhtProof {
            index: node_idx as NodeType,
            label,
            paths: path.path,
            locs: path.locs,
        })
    }

    fn generate_commit_proof(
        self: &Arc<Self>,
        fdir: &Path,
        neighbor: Option<&Path>,
        count: i64,
        c: i64,
        subfile: i64,
    ) -> Result<CommitProof> {
        let (cluster_size, _set_len) = {
            let s = self.state.read();
            (s.cluster_size, s.set_len)
        };
        if subfile < 0 || subfile > cluster_size + self.expanders.k - 1 {
            bail!("generate commit proof error: bad node index");
        }
        let n_bytes = (self.expanders.n as usize) * (HASH_SIZE as usize);
        let mut data = vec![0u8; n_bytes];
        let fpath = fdir.join(format!("{}-{}", FILE_NAME, subfile));
        read_file_to_buf(&fpath, &mut data)
            .with_context(|| "generate commit proof error")?;

        let mut node_tree = vec![0u8; self.expanders.n as usize * DEFAULT_HASH_SIZE];
        let mut parent_tree = vec![0u8; self.expanders.n as usize * DEFAULT_HASH_SIZE];

        let index = c % self.expanders.n;
        let path_proof = self.generate_path_proof(&mut node_tree, &data, index, c)?;

        let mut proof = CommitProof {
            node: path_proof,
            parents: Vec::new(),
            elders: Vec::new(),
        };

        let mut pdata = vec![0u8; n_bytes];
        let mut aux = vec![0u8; DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE];

        let mut subfile_local = subfile;
        let elders_len = (subfile / self.expanders.k * self.expanders.k / 2 + 1) as usize;
        proof.elders = vec![MhtProof::default_empty(); elders_len];

        if let Some(neighbor) = neighbor {
            read_file_to_buf(neighbor, &mut pdata)?;
            let aux_path_str = neighbor
                .to_string_lossy()
                .replacen(FILE_NAME, AUX_FILE, 1);
            read_file_to_buf(&PathBuf::from(aux_path_str), &mut aux)?;
            proof.elders[0] = self.get_path_proof_with_aux(&aux, &pdata, index, index)?;
        }

        if subfile == 0 {
            return Ok(proof);
        }

        let mut layer = subfile;
        if subfile >= self.expanders.k {
            let base_layer = (subfile - self.expanders.k / 2) / self.expanders.k;
            subfile_local = self.expanders.k;
            for i in 0..(self.expanders.k / 2) as usize {
                let fpath = fdir.join(format!("{}-{}", FILE_NAME, base_layer + (i * 2) as i64));
                let apath = fdir.join(format!("{}-{}", AUX_FILE, base_layer + (i * 2) as i64));
                read_file_to_buf(&fpath, &mut pdata)?;
                read_file_to_buf(&apath, &mut aux)?;
                proof.elders[i + 1] = self.get_path_proof_with_aux(
                    &aux,
                    &pdata,
                    index,
                    index + (base_layer + (i * 2) as i64) * self.expanders.n,
                )?;
            }
            layer = subfile; // unchanged, kept for clarity
        }
        let _ = layer;

        let mut node = Node::with_capacity(c as NodeType, self.expanders.d);
        calc_parents(&self.expanders, &mut node, &self.id, count, subfile);

        let fpath = fdir.join(format!("{}-{}", FILE_NAME, subfile_local - 1));
        read_file_to_buf(&fpath, &mut pdata)?;
        calc_light_mht_with_bytes(&mut parent_tree, &pdata, HASH_SIZE as usize);

        let lens = node.parents.len();
        let mut parent_proofs = vec![MhtProof::default_empty(); lens];
        for i in 0..lens {
            let pi = node.parents[i] as i64;
            let idx = pi % self.expanders.n;
            let path_proof;
            let mut label = vec![0u8; HASH_SIZE as usize];
            if pi >= subfile_local * self.expanders.n {
                label.copy_from_slice(
                    &data[idx as usize * HASH_SIZE as usize..(idx as usize + 1) * HASH_SIZE as usize],
                );
                path_proof = get_path_proof(&node_tree, &data, idx as usize, HASH_SIZE as usize)?;
            } else {
                label.copy_from_slice(
                    &pdata[idx as usize * HASH_SIZE as usize..(idx as usize + 1) * HASH_SIZE as usize],
                );
                path_proof =
                    get_path_proof(&parent_tree, &pdata, idx as usize, HASH_SIZE as usize)?;
            }
            let (mut paths, mut locs) = (path_proof.path, path_proof.locs);
            if node.parents[i] % 6 != 0 {
                paths.clear();
                locs.clear();
            }
            parent_proofs[i] = MhtProof {
                index: node.parents[i],
                label,
                paths,
                locs,
            };
        }
        proof.parents = parent_proofs;
        Ok(proof)
    }

    /// Generates a space-proof over file index range `[left, right)`.
    pub fn prove_space(
        self: &Arc<Self>,
        challenges: Vec<i64>,
        left: i64,
        right: i64,
    ) -> Result<SpaceProof> {
        let (cluster_size, _set_len, max_threads) = {
            let s = self.state.read();
            let cfg_guard = self.config.read();
            let max_proof = cfg_guard
                .as_ref()
                .map(|c| c.max_proof_thread)
                .unwrap_or(DEFAULT_MAX_PROOF_THREAD);
            (s.cluster_size, s.set_len, max_proof)
        };
        let chain_snap = self.get_chain_state();
        if challenges.is_empty()
            || right - left <= 0
            || left <= chain_snap.front
            || right > chain_snap.rear + 1
        {
            bail!("prove space error: bad challenge range");
        }

        let mut proof = SpaceProof {
            left,
            right,
            proofs: vec![Vec::new(); (right - left) as usize],
            roots: vec![Vec::new(); (right - left) as usize],
            wit_chains: Vec::new(),
        };

        let mut indexs: Vec<i64> = vec![0; (right - left) as usize];
        let mut threads = max_threads;
        if (right - left) < threads as i64 {
            threads = (right - left) as usize;
        }
        if threads == 0 {
            threads = 2;
        }
        let mut block = (right - left) as usize / threads;
        while block * threads < (right - left) as usize {
            block += 1;
        }

        // Build per-thread ranges.
        let ranges: Vec<(i64, i64)> = (0..threads)
            .map(|i| {
                let gl = left + (i * block) as i64;
                let gr = (left + ((i + 1) * block) as i64).min(right);
                (gl, gr)
            })
            .collect();

        // Parallel proof generation.
        let exp = self.expanders.clone();
        let prover = self.clone();
        let chals = challenges.clone();
        let per_thread_results: Vec<Result<Vec<(i64, Vec<u8>, Vec<MhtProof>)>>> = ranges
            .into_par_iter()
            .map(|(gl, gr)| {
                let mut local: Vec<(i64, Vec<u8>, Vec<MhtProof>)> = Vec::new();
                for fidx in gl..gr {
                    let mut data = vec![0u8; exp.n as usize * HASH_SIZE as usize];
                    prover.read_file_labels(
                        (fidx - 1) / cluster_size + 1,
                        (fidx - 1) % cluster_size,
                        &mut data,
                    )?;
                    let mut aux = vec![0u8; DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE];
                    prover.read_aux_data(
                        (fidx - 1) / cluster_size + 1,
                        (fidx - 1) % cluster_size,
                        &mut aux,
                    )?;
                    let mut mht = vec![0u8; aux.len()];
                    calc_light_mht_with_aux(&mut mht, &aux);
                    let root = get_root(&mht);
                    let mut file_proofs = Vec::with_capacity(chals.len());
                    for &cidx in &chals {
                        let idx = (cidx % exp.n) as usize;
                        let path_proof =
                            get_path_proof_with_aux(&data, &aux, idx, HASH_SIZE as usize)?;
                        let label = data[idx * HASH_SIZE as usize..(idx + 1) * HASH_SIZE as usize]
                            .to_vec();
                        file_proofs.push(MhtProof {
                            paths: path_proof.path,
                            locs: path_proof.locs,
                            index: cidx as NodeType,
                            label,
                        });
                    }
                    local.push((fidx, root, file_proofs));
                }
                Ok(local)
            })
            .collect();

        for r in per_thread_results {
            let chunk = r.with_context(|| "prove space error")?;
            for (fidx, root, fps) in chunk {
                let slot = (fidx - left) as usize;
                indexs[slot] = fidx;
                proof.roots[slot] = root;
                proof.proofs[slot] = fps;
            }
        }

        let chain_acc = chain_snap
            .acc
            .clone()
            .ok_or_else(|| anyhow!("prove space error: chain state not set"))?;
        proof.wit_chains = chain_acc
            .get_witness_chains(&indexs)
            .with_context(|| "prove space error")?;

        self.ctx.proofed.store(right - 1, Ordering::Release);
        // Drain del-ch if pending.
        let cs = self.chain_state.lock();
        if let Some((_, rx)) = &cs.del_ch {
            let _ = rx.try_recv();
        }
        Ok(proof)
    }

    /// Produces a deletion proof over the next `num` front-most files.
    pub fn prove_deletion(self: &Arc<Self>, num: i64) -> Result<DeletionProof> {
        if self.sync.load(Ordering::Acquire) {
            bail!("prove deletion error: syncing status, please try again");
        }
        if num <= 0 {
            bail!("prove deletion error: bad file number");
        }
        self.delete.store(true, Ordering::Release);
        {
            let s = self.state.read();
            if s.rear - s.front < num {
                bail!("prove deletion error: insufficient operating space");
            }
        }
        let (cluster_size, _) = {
            let s = self.state.read();
            (s.cluster_size, s.set_len)
        };
        let front = self.get_front();
        let mut roots: Vec<Vec<u8>> = vec![Vec::new(); num as usize];
        let mut data = vec![0u8; self.expanders.n as usize * HASH_SIZE as usize];
        let mut aux = vec![0u8; DEFAULT_AUX_SIZE * DEFAULT_HASH_SIZE];
        let mut mht = vec![0u8; aux.len()];
        for i in 1..=num {
            let cluster = (front + i - 1) / cluster_size + 1;
            let subfile = (front + i - 1) % cluster_size;
            self.read_file_labels(cluster, subfile, &mut data)
                .with_context(|| "prove deletion error")?;
            self.read_aux_data(cluster, subfile, &mut aux)
                .with_context(|| "prove deletion error")?;
            calc_light_mht_with_aux(&mut mht, &aux);
            roots[(i - 1) as usize] = get_root(&mht);
        }
        let mgr = self
            .acc_manager
            .read()
            .clone()
            .ok_or_else(|| anyhow!("acc manager not initialised"))?;
        let (wits, accs) = mgr
            .delete_elements_and_proof(num as usize)
            .with_context(|| "prove deletion error")?;
        Ok(DeletionProof {
            roots,
            wit_chain: wits,
            acc_path: accs,
        })
    }

    // -----------------------------------------------------------------------
    // Disk housekeeping
    // -----------------------------------------------------------------------

    pub(crate) fn organize_files(self: &Arc<Self>, idx: i64, num: i64) -> Result<()> {
        let (cluster_size, set_len, file_size, idle_file_path) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .ok_or_else(|| anyhow!("config not set"))?
                .clone_basic();
            (s.cluster_size, s.set_len, cfg.3, cfg.2)
        };
        let dir =
            Path::new(&idle_file_path).join(format!("{}-{}", SET_DIR_NAME, idx / (cluster_size * set_len) + 1));
        let mut i = idx + 1;
        while i <= idx + num {
            for j in 0..self.expanders.k {
                let name = dir
                    .join(format!("{}-{}", CLUSTER_DIR_NAME, (i - 1) / cluster_size + 1))
                    .join(format!("{}-{}", FILE_NAME, j));
                let _ = delete_file(&name);
                let name = dir
                    .join(format!("{}-{}", CLUSTER_DIR_NAME, (i - 1) / cluster_size + 1))
                    .join(format!("{}-{}", AUX_FILE, j));
                let _ = delete_file(&name);
            }
            i += 8;
        }
        let _ = delete_file(dir.join(COMMIT_FILE));
        let mut s = self.state.write();
        s.space += num / cluster_size * self.expanders.k * file_size;
        Ok(())
    }

    fn delete_files(self: &Arc<Self>) -> Result<()> {
        let idle_file_path = self
            .config
            .read()
            .as_ref()
            .ok_or_else(|| anyhow!("config not set"))?
            .idle_file_path
            .clone();
        let (front, set_len, cluster_size) = {
            let s = self.state.read();
            (s.front, s.set_len, s.cluster_size)
        };
        // Notify any in-flight prover that we are deleting.
        {
            let cs = self.chain_state.lock();
            let proofed = self.ctx.proofed.load(Ordering::Acquire);
            if cs.challenging && proofed < front {
                if let Some((s, _)) = &cs.del_ch {
                    let _ = s.try_send(());
                }
            }
        }

        let indexs = [
            (front - 1) / (set_len * cluster_size) + 1,
            (front - 1) / cluster_size + 1,
            (front - 1) % cluster_size + self.expanders.k,
        ];
        deleter(&idle_file_path, &indexs)
    }

    /// Scans the idle-files directory to determine how many files are present.
    fn calc_generated_file(self: &Arc<Self>, dir: &str) -> Result<i64> {
        let (set_len, cluster_size, file_size, rear) = {
            let s = self.state.read();
            let cfg = self
                .config
                .read()
                .as_ref()
                .map(|c| c.file_size)
                .unwrap_or(0);
            (s.set_len, s.cluster_size, cfg, s.rear)
        };
        let mut count: i64 = 0;
        let file_total_size = file_size * (self.expanders.k + cluster_size) * 1024 * 1024;
        let root_size = (set_len * (self.expanders.k + cluster_size) + 1) * DEFAULT_HASH_SIZE as i64;

        if !Path::new(dir).exists() {
            return Ok(0);
        }
        let entries: Vec<_> = std::fs::read_dir(dir)
            .with_context(|| "read idle dir error")?
            .filter_map(|e| e.ok())
            .collect();
        let mut next: i64 = 1;
        for entry in &entries {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            let parts: Vec<&str> = name.split('-').collect();
            if parts.len() < 3 {
                continue;
            }
            let idx: i64 = match parts[2].parse() {
                Ok(v) => v,
                Err(_) => continue,
            };
            if idx != rear / (set_len * cluster_size) + next {
                continue;
            }
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }
            let roots_path = path.join(COMMIT_FILE);
            let roots_meta = match std::fs::metadata(&roots_path) {
                Ok(m) => m,
                Err(_) => continue,
            };
            if roots_meta.len() as i64 != root_size {
                continue;
            }
            let clusters: Vec<_> = match std::fs::read_dir(&path) {
                Ok(it) => it.filter_map(|e| e.ok()).collect(),
                Err(_) => continue,
            };
            let mut i = 0;
            for cluster in clusters {
                let cp = cluster.path();
                if !cp.is_dir() {
                    continue;
                }
                let mut size: i64 = 0;
                let files = match std::fs::read_dir(&cp) {
                    Ok(it) => it,
                    Err(_) => continue,
                };
                for file in files.filter_map(|e| e.ok()) {
                    let meta = match file.metadata() {
                        Ok(m) => m,
                        Err(_) => continue,
                    };
                    if !meta.is_dir() && meta.len() as i64 >= MINI_FILE_SIZE {
                        size += meta.len() as i64;
                    }
                }
                if size == file_total_size {
                    count += cluster_size;
                    i += 1;
                }
            }
            if i == set_len as i32 {
                next += 1;
            }
        }
        Ok(count)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

impl ResolvedConfig {
    /// Returns `(acc_path, chall_acc_path, idle_file_path, file_size)`.
    fn clone_basic(&self) -> (String, String, String, i64) {
        (
            self.acc_path.clone(),
            self.chall_acc_path.clone(),
            self.idle_file_path.clone(),
            self.file_size,
        )
    }
}

struct AutoFlag<'a>(&'a AtomicBool);
impl<'a> AutoFlag<'a> {
    fn new(flag: &'a AtomicBool) -> Self {
        Self(flag)
    }
}
impl Drop for AutoFlag<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

/// Helper used by `MhtProof::default_empty` to spell out the default
/// without requiring `Default`-bound `NodeType` arithmetic.
impl MhtProof {
    fn default_empty() -> Self {
        MhtProof {
            index: 0,
            label: Vec::new(),
            paths: Vec::new(),
            locs: Vec::new(),
        }
    }
}

impl CommitProof {
    fn default_empty() -> Self {
        CommitProof {
            node: MhtProof::default_empty(),
            parents: Vec::new(),
            elders: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// recursive `deleter` (matches Go semantics)
// ---------------------------------------------------------------------------

fn deleter(root_dir: &str, indexs: &[i64]) -> Result<()> {
    if indexs.is_empty() {
        return Ok(());
    }
    let entries = match std::fs::read_dir(root_dir) {
        Ok(v) => v,
        Err(_) => return Ok(()),
    };
    for entry in entries.filter_map(|e| e.ok()) {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let parts: Vec<&str> = name.split('-').collect();
        let idx: i64 = match parts.last().and_then(|s| s.parse().ok()) {
            Some(v) => v,
            None => continue,
        };
        let path = entry.path();
        let is_dir = path.is_dir();
        if idx < indexs[0] || (idx == indexs[0] && !is_dir) {
            let _ = delete_dir(&path);
            continue;
        }
        if idx != indexs[0] {
            continue;
        }
        deleter(path.to_string_lossy().as_ref(), &indexs[1..])?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// re-exports
// ---------------------------------------------------------------------------

pub use crate::acc::multi_level_acc::WitnessNode as ProverWitnessNode;
#[allow(dead_code)]
fn _link_wit_node(_w: &WitnessNode) {}
