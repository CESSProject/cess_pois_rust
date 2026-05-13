//! # Utility Functions
//!
//! Low-level helpers shared across the verifier and prover:
//! - File I/O (read / write / save / delete / copy)
//! - Byte slice composition helpers
//! - RSA accumulator key parsing
//! - Free-disk-space lookup
//! - Go-compatible base64 byte-slice JSON encoding (see [`json_bytes`])
//!
//! These mirror the helpers found in `util/utils.go` in the Go
//! reference implementation.

pub mod json_bytes;

use std::fs::{self, File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;

use crate::acc::{self, RsaKey};
use anyhow::{anyhow, Context, Result};
use num_bigint_dig::BigUint;
use rand::Rng;
use sysinfo::Disks;

const CHARS: &[u8] =
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890";

/// Copies multiple byte slices sequentially into a target buffer.
///
/// Source slices that would not fit into the remaining target space
/// are skipped (matches the semantics of the Go `CopyData`).
pub fn copy_data(target: &mut [u8], src: &[&[u8]]) {
    let mut count = 0;
    let lens = target.len();

    for d in src {
        let l = d.len();
        if l == 0 || l + count > lens {
            continue;
        }
        target[count..count + l].copy_from_slice(d);
        count += l;
    }
}

/// XOR-merges source slices into `target`.
///
/// Source slices shorter than the target are skipped.
pub fn add_data(target: &mut [u8], src: &[&[u8]]) {
    let target_len = target.len();
    for s in src {
        if s.len() < target_len {
            continue;
        }
        for (i, elem) in target.iter_mut().enumerate() {
            *elem ^= s[i];
        }
    }
}

/// Zeroes a byte buffer in place.
pub fn clear_data(target: &mut [u8]) {
    for element in target.iter_mut() {
        *element = 0;
    }
}

/// Generates a pseudo-random alphanumeric string of length `len_num`.
pub fn rand_string(len_num: usize) -> String {
    let mut rng = rand::thread_rng();
    let mut out = String::with_capacity(len_num);
    for _ in 0..len_num {
        let idx = rng.gen_range(0..CHARS.len());
        out.push(CHARS[idx] as char);
    }
    out
}

/// Writes the provided sequence of byte vectors to a file end-to-end.
///
/// Used for saving proof artefacts that consist of multiple fixed-size
/// records (e.g. Merkle tree commit roots).
pub fn save_proof_file<P: AsRef<Path>>(path: P, data: &[Vec<u8>]) -> Result<()> {
    let file = File::create(&path).with_context(|| "save proof file error")?;
    let mut writer = BufWriter::new(file);
    for d in data {
        writer
            .write_all(d)
            .with_context(|| "write proof file error")?;
    }
    writer.flush().with_context(|| "flush proof file error")?;
    Ok(())
}

/// Reads `num` records of `len` bytes each from `path`.
pub fn read_proof_file<P: AsRef<Path>>(path: P, num: usize, len: usize) -> Result<Vec<Vec<u8>>> {
    if num == 0 {
        return Err(anyhow!("read proof file error: illegal label number"));
    }
    let file = File::open(&path).with_context(|| "read proof file error")?;
    let mut reader = BufReader::new(file);
    let mut data = Vec::with_capacity(num);
    for _ in 0..num {
        let mut label = vec![0u8; len];
        reader
            .read_exact(&mut label)
            .with_context(|| "read proof file error")?;
        data.push(label);
    }
    Ok(data)
}

/// Removes a directory tree (no-op if missing).
pub fn delete_dir<P: AsRef<Path>>(dir: P) -> Result<()> {
    if !dir.as_ref().exists() {
        return Ok(());
    }
    fs::remove_dir_all(&dir).with_context(|| "delete dir error")?;
    Ok(())
}

/// Writes `data` to `path`, creating or truncating the file.
pub fn save_file<P: AsRef<Path>>(path: P, data: &[u8]) -> Result<()> {
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&path)
        .with_context(|| "save file error")?;
    let mut writer = BufWriter::new(file);
    writer.write_all(data).with_context(|| "save file error")?;
    writer.flush().with_context(|| "save file error")?;
    Ok(())
}

/// Deletes a single file (no-op if missing).
pub fn delete_file<P: AsRef<Path>>(path: P) -> Result<()> {
    if !path.as_ref().exists() {
        return Ok(());
    }
    fs::remove_file(&path).with_context(|| "delete file error")?;
    Ok(())
}

/// Reads exactly `buf.len()` bytes from `path` into `buf`.
pub fn read_file_to_buf<P: AsRef<Path>>(path: P, buf: &mut [u8]) -> Result<()> {
    if buf.is_empty() {
        return Ok(());
    }
    let file = File::open(&path).with_context(|| "read file to buf error")?;
    let mut reader = BufReader::new(file);
    reader
        .read_exact(buf)
        .with_context(|| "read file to buf error")?;
    Ok(())
}

/// Reads a file's full contents into memory.
pub fn read_file<P: AsRef<Path>>(path: P) -> Result<Vec<u8>> {
    fs::read(&path).with_context(|| "read file error")
}

/// Copies a single file. Overwrites the destination.
pub fn copy_file<P: AsRef<Path>, Q: AsRef<Path>>(src: P, des: Q) -> Result<()> {
    fs::copy(&src, &des).with_context(|| "copy file error")?;
    Ok(())
}

/// Recursively copies all non-directory files from `src` to `des`,
/// recreating `des` from scratch first.
pub fn copy_files<P: AsRef<Path>, Q: AsRef<Path>>(src: P, des: Q) -> Result<()> {
    if des.as_ref().exists() {
        fs::remove_dir_all(&des).with_context(|| "copy files: remove dst error")?;
    }
    fs::create_dir_all(&des).with_context(|| "copy files: mkdir dst error")?;

    if !src.as_ref().exists() {
        return Ok(());
    }
    for entry in fs::read_dir(&src).with_context(|| "copy files: read src error")? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            continue;
        }
        let dst = des.as_ref().join(entry.file_name());
        fs::copy(entry.path(), dst).with_context(|| "copy files: copy entry error")?;
    }
    Ok(())
}

/// Returns the amount of free disk space (in bytes) on the volume containing `dir`.
pub fn get_dir_free_space<P: AsRef<Path>>(dir: P) -> Result<u64> {
    let target = fs::canonicalize(&dir).unwrap_or_else(|_| dir.as_ref().to_path_buf());
    let disks = Disks::new_with_refreshed_list();
    let mut best: Option<(usize, u64)> = None;
    for disk in disks.iter() {
        let mount = disk.mount_point().to_path_buf();
        if target.starts_with(&mount) {
            let mlen = mount.as_os_str().len();
            if best.map(|(l, _)| mlen > l).unwrap_or(true) {
                best = Some((mlen, disk.available_space()));
            }
        }
    }
    best.map(|(_, free)| free)
        .ok_or_else(|| anyhow!("could not find a disk containing {}", dir.as_ref().display()))
}

/// Parses an RSA accumulator key from a file (see `get_key_from_bytes`).
pub fn parse_key(path: &str) -> Result<RsaKey> {
    let data = fs::read(path)?;
    Ok(get_key_from_bytes(&data))
}

/// Constructs an RSA accumulator key from raw bytes.
///
/// The expected layout is:
///   - 8 bytes BE: length of `n`
///   - 8 bytes BE: length of `g`
///   - `n` bytes:  modulus
///   - `g` bytes:  generator
///
/// On parse failure, a fresh key is generated.
fn get_key_from_bytes(data: &[u8]) -> RsaKey {
    if data.len() < 16 {
        return acc::rsa_keygen(2048);
    }
    let nl = u64::from_be_bytes(data[..8].try_into().unwrap());
    let gl = u64::from_be_bytes(data[8..16].try_into().unwrap());
    if nl == 0 || gl == 0 || data.len() - 16 != (nl + gl) as usize {
        return acc::rsa_keygen(2048);
    }
    let n = BigUint::from_bytes_be(&data[16..16 + nl as usize]);
    let g = BigUint::from_bytes_be(&data[16 + nl as usize..]);
    RsaKey::new(n, g)
}
