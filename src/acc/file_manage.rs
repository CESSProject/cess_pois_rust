//! # On-disk persistence for sub-accumulator state
//!
//! Mirrors `acc/file_manage.go` from the Go reference.  Each sub-accumulator
//! is serialised as JSON into a file named `sub-acc-<index>`, with an
//! optional `backup-sub-acc-<index>` sibling used to make multi-step
//! updates recoverable.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

use crate::util::{copy_file, delete_file, read_file, save_file};

/// Default filename prefix for an active sub-accumulator.
pub const DEFAULT_NAME: &str = "sub-acc";
/// Default filename prefix for a backup of a sub-accumulator file.
pub const DEFAULT_BACKUP_NAME: &str = "backup-sub-acc";

/// Default directory used when callers don't specify a path.
pub const DEFAULT_PATH: &str = "./acc/";

/// Default permission bits (POSIX-style) for created accumulator directories.
pub const DEFAULT_DIR_PERM: u32 = 0o755;

/// Maximum number of leaves per sub-accumulator.
pub const DEFAULT_ELEMS_NUM: usize = 256;

/// Number of levels in the multi-level accumulator tree.
pub const DEFAULT_LEVEL: usize = 3;

/// Serialised pair of element values and corresponding witnesses for a single
/// sub-accumulator.
///
/// The JSON layout mirrors Go's `acc.AccData` exactly (`[]byte` fields are
/// serialised as base64-encoded strings).
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct AccData {
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub values: Vec<Vec<u8>>,
    #[serde(default, with = "crate::util::json_bytes::bytes_vec")]
    pub wits: Vec<Vec<u8>>,
}

fn acc_path(dir: &str, index: i64) -> PathBuf {
    Path::new(dir).join(format!("{}-{}", DEFAULT_NAME, index))
}

fn backup_path(dir: &str, index: i64) -> PathBuf {
    Path::new(dir).join(format!("{}-{}", DEFAULT_BACKUP_NAME, index))
}

/// Writes a sub-accumulator to disk as JSON.
pub fn save_acc_data(dir: &str, index: i64, elems: Vec<Vec<u8>>, wits: Vec<Vec<u8>>) -> Result<()> {
    let data = AccData { values: elems, wits };
    let bytes = serde_json::to_vec(&data).with_context(|| "save element data error")?;
    save_file(acc_path(dir, index), &bytes).with_context(|| "save element data error")
}

/// Reads the active sub-accumulator with the given index.
pub fn read_acc_data(dir: &str, index: i64) -> Result<AccData> {
    read_data(&acc_path(dir, index))
}

/// Reads the backup sub-accumulator with the given index (if any).
pub fn read_backup(dir: &str, index: i64) -> Result<AccData> {
    read_data(&backup_path(dir, index))
}

fn read_data(path: &Path) -> Result<AccData> {
    let data = read_file(path).with_context(|| "read element data error")?;
    let acc: AccData =
        serde_json::from_slice(&data).with_context(|| "read element data error")?;
    Ok(acc)
}

/// Deletes every accumulator file whose trailing index is `<= last`.
pub fn delete_acc_data(dir: &str, last: i64) -> Result<()> {
    let entries = fs::read_dir(dir).with_context(|| "delete element data error")?;
    for entry in entries {
        let entry = entry.with_context(|| "delete element data error")?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let parts: Vec<&str> = name.rsplitn(2, '-').collect();
        if parts.is_empty() {
            continue;
        }
        let idx: i64 = match parts[0].parse() {
            Ok(v) => v,
            Err(_) => continue,
        };
        if idx <= last {
            let p = Path::new(dir).join(name.as_ref());
            delete_file(&p).with_context(|| "delete element data error")?;
        }
    }
    Ok(())
}

/// Removes a single backup file (no-op if missing).
pub fn clean_backup(dir: &str, index: i64) -> Result<()> {
    delete_file(backup_path(dir, index)).with_context(|| "clean backup error")
}

/// Copies the active sub-accumulator file `index` to its backup slot.
pub fn backup_acc_data(dir: &str, index: i64) -> Result<()> {
    let src = acc_path(dir, index);
    let dst = backup_path(dir, index);
    if !src.exists() {
        return Ok(());
    }
    copy_file(src, dst).with_context(|| "backup element data error")
}

/// Copies the active sub-accumulator file at `index` from `src` directory
/// to `des` directory, used to snapshot challenge state.
pub fn backup_acc_data_for_chall(src: &str, des: &str, index: i64) -> Result<()> {
    let s = acc_path(src, index);
    let d = acc_path(des, index);
    if !s.exists() {
        return Ok(());
    }
    copy_file(s, d).with_context(|| "backup acc data for challenge error")
}

/// Restores `sub-acc-<index>` from its backup, if a backup exists.
pub fn recovery_acc_data(dir: &str, index: i64) -> Result<()> {
    let backup = backup_path(dir, index);
    let active = acc_path(dir, index);
    if !backup.exists() {
        return Ok(());
    }
    fs::rename(&backup, &active).with_context(|| "recovery element data error")?;
    Ok(())
}

/// Ensures a directory exists, creating it (and parents) with [`DEFAULT_DIR_PERM`].
pub fn ensure_dir(dir: &str) -> Result<()> {
    if Path::new(dir).exists() {
        return Ok(());
    }
    fs::create_dir_all(dir).with_context(|| "create acc dir error")?;
    Ok(())
}
