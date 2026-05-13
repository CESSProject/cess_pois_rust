//! Generates a single idle file set under `/tmp/idle-rust` using the
//! same `(K, N, D, miner_id, start, set_len)` parameters as the Go
//! `idlegen.go` test fixture, so the two outputs can be diff'd
//! directory-for-directory and byte-for-byte.

use std::fs;

use cess_pois_rust::expanders::Expanders;
use cess_pois_rust::tree::init_mht_pool;

fn main() -> anyhow::Result<()> {
    const K: i64 = 8;
    const N: i64 = 1024 * 16;
    const D: i64 = 64;
    const SET_LEN: i64 = 2;
    const START: i64 = 1;

    let miner_id = &b"compat-miner-id-32-bytes-padding"[..32];

    let dir = "/tmp/idle-rust";
    let _ = fs::remove_dir_all(dir);
    fs::create_dir_all(dir)?;

    init_mht_pool(N as usize);
    let exp = Expanders::new(K, N, D);
    exp.generate_idle_file_set(miner_id, START, SET_LEN, dir)?;
    println!("ok");
    Ok(())
}
