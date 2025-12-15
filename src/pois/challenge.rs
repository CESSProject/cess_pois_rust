//! # Challenge Verification Handle
//!
//! This module provides a factory function for constructing
//! **stateful challenge-verification closures** used in expander-
//! based proof protocols.
//!
//! The generated closure deterministically derives expected
//! challenge ranges based on:
//! - Miner identity
//! - TEE identity
//! - Challenge parameters
//! - Previous hash output
//!
//! It is designed to be invoked sequentially and maintains
//! internal state across invocations.

use crate::expanders::{self, generate_idle_file::get_hash};

/// Creates a new challenge verification handle.
///
/// The returned closure validates whether a given `(left, right)`
/// range matches the expected challenge range derived from
/// cryptographic hashing and expander-based indexing.
///
/// The closure is **stateful** and must be called sequentially
/// in the correct order.
///
/// # Parameters
/// - `miner_id`: Unique miner identifier
/// - `tee_id`: Trusted execution environment identifier
/// - `chal`: Challenge parameters
/// - `front`: Start index of the challenge range
/// - `rear`: End index of the challenge range
/// - `proof_num`: Maximum number of proof rounds
///
/// # Returns
/// - `Some(closure)` if parameters are valid
/// - `None` if the number of required rounds exceeds `proof_num`
pub fn new_challenge_handle(
    miner_id: &[u8],
    tee_id: &[u8],
    chal: &[i64],
    front: i64,
    rear: i64,
    proof_num: i64,
) -> Option<impl FnMut(&[u8], i64, i64) -> bool> {
    let bytes_chal = expanders::get_bytes_slice(chal);
    let front_size = miner_id.len() + tee_id.len() + bytes_chal.len();
    let mut source = Vec::with_capacity(front_size + 64);
    source.extend_from_slice(miner_id);
    source.extend_from_slice(tee_id);
    source.extend_from_slice(&bytes_chal);
    source.extend_from_slice(&[0; 64]);

    let file_num: i64 = 256;
    let group_size: i64 = 16;

    let start = front / file_num;
    let mut count: i64 = 0;
    let total = (rear - front + front % file_num - 1) / (file_num * group_size) + 1;

    if total > proof_num {
        return None;
    }

    Some(move |prior_hash: &[u8], left: i64, right: i64| -> bool {
        if !prior_hash.is_empty() {
            source[front_size..].copy_from_slice(prior_hash);
        }
        let mut max = group_size - 1;
        if count == total - 1 {
            max = rear / file_num - (start + count * group_size)
        }
        let hash = get_hash(&source);
        let v = expanders::bytes_to_node_value(&hash, max) as i64;
        let mut l = (start + count * group_size + v) * file_num + 1;
        let r = ((l - 1) / file_num + 1) * file_num + 1;
        if l < front {
            l = front + 1;
        }
        count += 1;
        if l != left || r != right {
            return false;
        }
        true
    })
}
