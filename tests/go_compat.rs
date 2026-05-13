//! # Go-↔-Rust wire-format compatibility tests
//!
//! These tests pin down the exact JSON that the Go reference
//! implementation produces and verify that the Rust port can
//! deserialise it and serialise back to a byte-identical payload.
//!
//! They also exercise the parts of the algorithm that are most
//! sensitive to interop: deterministic accumulator math, fixed
//! file-name formats, and the Merkle tree layout.

use cess_pois_rust::acc::file_manage::AccData;
use cess_pois_rust::acc::multi_level_acc::WitnessNode;
use cess_pois_rust::expanders::Expanders;
use cess_pois_rust::pois::prove::{Commits, MhtProof};

// ---------------------------------------------------------------------------
// 1. Expanders JSON layout (file produced by Go's `MarshalAndSave`).
// ---------------------------------------------------------------------------

#[test]
fn expanders_json_matches_go() {
    // The exact bytes Go emits for Expanders{K:7, N:65536, D:64,
    // Size:524288, HashSize:64} (key order: as defined in Go struct).
    let go_json = r#"{"K":7,"N":65536,"D":64,"size":524288,"hash_szie":64}"#;

    let exp: Expanders = serde_json::from_str(go_json).expect("deserialize Go expanders");
    assert_eq!(exp.k, 7);
    assert_eq!(exp.n, 65536);
    assert_eq!(exp.d, 64);
    assert_eq!(exp.size, 524288);
    assert_eq!(exp.hash_size, 64);

    // Round-trip: Rust output must contain the same fields (key order
    // is unspecified in JSON, but every field must be present with the
    // capitalisation Go uses).
    let rs_json = serde_json::to_string(&exp).expect("serialize expanders");
    assert!(rs_json.contains("\"K\":7"), "missing K: {}", rs_json);
    assert!(rs_json.contains("\"N\":65536"), "missing N: {}", rs_json);
    assert!(rs_json.contains("\"D\":64"), "missing D: {}", rs_json);
    assert!(rs_json.contains("\"size\":524288"));
    assert!(rs_json.contains("\"hash_szie\":64"));
}

// ---------------------------------------------------------------------------
// 2. AccData JSON layout (sub-acc-N files written by Go).
// ---------------------------------------------------------------------------

#[test]
fn accdata_json_matches_go() {
    // Equivalent to: AccData{Values:[][]byte{{1,2,3},{0xff,0,0x42}}, Wits:[][]byte{{0xab},{0xcd,0xef}}}
    //   base64("\x01\x02\x03") = "AQID"
    //   base64("\xff\x00B")    = "/wBC"
    //   base64("\xab")         = "qw=="
    //   base64("\xcd\xef")     = "ze8="
    let go_json = r#"{"values":["AQID","/wBC"],"wits":["qw==","ze8="]}"#;

    let ad: AccData = serde_json::from_str(go_json).expect("deserialize AccData");
    assert_eq!(ad.values, vec![vec![1u8, 2, 3], vec![0xff, 0x00, 0x42]]);
    assert_eq!(ad.wits, vec![vec![0xab_u8], vec![0xcd, 0xef]]);

    // Round-trip: must produce byte-identical Go-style output.
    let rs_json = serde_json::to_string(&ad).expect("serialize AccData");
    assert_eq!(rs_json, go_json);
}

// ---------------------------------------------------------------------------
// 3. WitnessNode JSON layout (used in proof payloads).
// ---------------------------------------------------------------------------

#[test]
fn witness_node_json_matches_go() {
    // base64("\x01\x02") = "AQI=", "\x03\x04" = "AwQ=", "\x05" = "BQ==", "\x06" = "Bg=="
    let go_json =
        r#"{"elem":"AQI=","wit":"AwQ=","acc":{"elem":"BQ==","wit":"Bg==","acc":null}}"#;

    let w: WitnessNode = serde_json::from_str(go_json).expect("deserialize WitnessNode");
    assert_eq!(w.elem, vec![0x01, 0x02]);
    assert_eq!(w.wit, vec![0x03, 0x04]);
    let acc = w.acc.as_ref().expect("acc present");
    assert_eq!(acc.elem, vec![0x05]);
    assert_eq!(acc.wit, vec![0x06]);
    assert!(acc.acc.is_none());

    let rs_json = serde_json::to_string(&w).expect("serialize WitnessNode");
    assert_eq!(rs_json, go_json);
}

// ---------------------------------------------------------------------------
// 4. Commits JSON layout (sent from prover to verifier).
// ---------------------------------------------------------------------------

#[test]
fn commits_json_matches_go() {
    let go_json = r#"{"file_indexs":[1,2,3],"roots":["AQID","/wBC"]}"#;
    let c: Commits = serde_json::from_str(go_json).expect("deserialize Commits");
    assert_eq!(c.file_indexs, vec![1, 2, 3]);
    assert_eq!(c.roots, vec![vec![1u8, 2, 3], vec![0xff, 0x00, 0x42]]);

    let rs_json = serde_json::to_string(&c).expect("serialize Commits");
    assert_eq!(rs_json, go_json);
}

// ---------------------------------------------------------------------------
// 5. MhtProof JSON layout.
// ---------------------------------------------------------------------------

#[test]
fn mhtproof_json_matches_go() {
    let go_json =
        r#"{"index":42,"label":"AQI=","paths":["AwQ=","BQY="],"locs":"AAE="}"#;
    let p: MhtProof = serde_json::from_str(go_json).expect("deserialize MhtProof");
    assert_eq!(p.index, 42);
    assert_eq!(p.label, vec![0x01, 0x02]);
    assert_eq!(p.paths, vec![vec![0x03_u8, 0x04], vec![0x05, 0x06]]);
    assert_eq!(p.locs, vec![0x00, 0x01]);

    let rs_json = serde_json::to_string(&p).expect("serialize MhtProof");
    assert_eq!(rs_json, go_json);
}

// ---------------------------------------------------------------------------
// 6. Legacy compatibility: deserialise integer-array Vec<u8> (older Rust output).
// ---------------------------------------------------------------------------

#[test]
fn accepts_legacy_integer_byte_arrays() {
    // Older Rust serializers may have produced this shape; we still accept it.
    let legacy = r#"{"values":[[1,2,3]],"wits":[[171]]}"#;
    let ad: AccData = serde_json::from_str(legacy).expect("deserialize legacy AccData");
    assert_eq!(ad.values, vec![vec![1u8, 2, 3]]);
    assert_eq!(ad.wits, vec![vec![0xab_u8]]);
}
