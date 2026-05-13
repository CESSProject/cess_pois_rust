//! # Go-compatible byte-slice JSON serialization helpers
//!
//! Go's `encoding/json` marshals `[]byte` as a **base64-encoded string**,
//! while serde-json marshals `Vec<u8>` as a JSON array of integers.
//! This module provides drop-in `#[serde(with = ...)]` helpers that match
//! Go's behavior so that files written by Go can be read by Rust and
//! vice versa.

use base64::engine::general_purpose::STANDARD;
use base64::Engine;
use serde::de::Error as DeError;
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serializer};

/// Serde helper for a single `Vec<u8>` field.  Encodes as base64 string.
///
/// Apply with `#[serde(with = "crate::util::json_bytes::bytes")]`.
pub mod bytes {
    use super::*;

    pub fn serialize<S: Serializer>(value: &Vec<u8>, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&STANDARD.encode(value))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<u8>, D::Error> {
        // Accept both base64 string (Go) and integer-array (legacy Rust) inputs.
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum BytesIn {
            B64(String),
            Arr(Vec<u8>),
            Null, // empty
        }
        match BytesIn::deserialize(d)? {
            BytesIn::B64(s) => STANDARD.decode(&s).map_err(D::Error::custom),
            BytesIn::Arr(v) => Ok(v),
            BytesIn::Null => Ok(Vec::new()),
        }
    }
}

/// Serde helper for `Vec<Vec<u8>>` — each inner vec is base64-encoded.
///
/// Apply with `#[serde(with = "crate::util::json_bytes::bytes_vec")]`.
pub mod bytes_vec {
    use super::*;

    pub fn serialize<S: Serializer>(value: &Vec<Vec<u8>>, s: S) -> Result<S::Ok, S::Error> {
        let mut seq = s.serialize_seq(Some(value.len()))?;
        for inner in value {
            seq.serialize_element(&STANDARD.encode(inner))?;
        }
        seq.end()
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Vec<u8>>, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Item {
            B64(String),
            Arr(Vec<u8>),
        }
        let items: Vec<Item> = Vec::deserialize(d)?;
        items
            .into_iter()
            .map(|item| match item {
                Item::B64(s) => STANDARD.decode(&s).map_err(D::Error::custom),
                Item::Arr(v) => Ok(v),
            })
            .collect()
    }
}
