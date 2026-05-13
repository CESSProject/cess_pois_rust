//! Cross-checks the Rust `acc::generate_acc_from_scratch` and the Go
//! prover-side `NewChallengeHandle` formula against the Go reference.
//!
//! Run alongside `gocompat/acc_chal.go` — outputs must match line-for-line.

use cess_pois_rust::acc::{generate_acc_from_scratch, RsaKey};
use cess_pois_rust::expanders::{bytes_to_int64, get_bytes_slice};
use cess_pois_rust::expanders::generate_idle_file::get_hash;
use num_bigint_dig::BigUint;

fn main() {
    // Same RSA key.
    let n = BigUint::parse_bytes(
        b"a1b2c3d4e5f60718293a4b5c6d7e8f9012345678901234567890abcdefabcdef",
        16,
    )
    .unwrap();
    let g = BigUint::from(2u32);
    let key = RsaKey::new(n, g);

    let elems = vec![vec![0x01u8, 0x02], vec![0x03, 0x04]];
    let out = generate_acc_from_scratch(&key, &elems);
    println!("ACC={}", hex::encode(out));

    // Same challenge inputs as Go.
    let miner_id = &b"miner-32-bytes-padding----------"[..32];
    let tee_id = &b"tee-32-bytes-padding------------"[..32];
    let chal: Vec<i64> = vec![42, 7, 9];
    let front: i64 = 0;
    let rear: i64 = 8192;

    let bytes_chal = get_bytes_slice(&chal);
    let front_size = miner_id.len() + tee_id.len() + bytes_chal.len();
    let mut source = Vec::with_capacity(front_size + 32);
    source.extend_from_slice(miner_id);
    source.extend_from_slice(tee_id);
    source.extend_from_slice(&bytes_chal);
    source.extend_from_slice(&[0u8; 32]);

    let file_num: i64 = 256;
    let group_size: i64 = 16;
    let start = front / file_num;
    let mut count: i64 = 0;
    let total = (rear - front + front % file_num - 1) / (file_num * group_size) + 1;

    let priors: Vec<Vec<u8>> = vec![
        Vec::new(),
        vec![0xab, 0xcd, 0xef],
        vec![0x12, 0x34, 0x56, 0x78],
    ];

    for prior in &priors {
        if count >= total {
            break;
        }
        let mut max = group_size - 1;
        if count == total - 1 {
            max = rear / file_num - (start + count * group_size);
        }
        if !prior.is_empty() {
            source[front_size..front_size + prior.len()].copy_from_slice(prior);
        }
        let hash = get_hash(&source);
        let v = bytes_to_int64(&hash, max.max(1));
        let mut l = (start + count * group_size + v) * file_num + 1;
        let r = ((l - 1) / file_num + 1) * file_num + 1;
        if l < front {
            l = front + 1;
        }
        count += 1;
        println!("CHAL count={} left={} right={}", count, l, r);
    }
}
