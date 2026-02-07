use vstd::prelude::*;
use crate::codec::compact::*;

verus! {

// ============================================================================
// SCALE encoding of Vec<u8>
//
// Reference: parity-scale-codec
//
// Encode: compact_encode(len as u32) ++ raw_bytes
// Decode: compact_decode → len, then read len bytes
//
// Precondition: v.len() <= u32::MAX (SCALE uses compact<u32> for lengths)
// ============================================================================

/// Encode Vec<u8> in SCALE format: compact length prefix followed by raw bytes
pub open spec fn vec_u8_encode(v: Seq<u8>) -> Seq<u8>
    recommends v.len() <= u32::MAX as int,
{
    compact_encode(v.len() as u32) + v
}

/// Decode Vec<u8> from SCALE format.
/// Returns Some(decoded_bytes) or None on failure.
pub open spec fn vec_u8_decode(bytes: Seq<u8>) -> Option<Seq<u8>> {
    match compact_decode(bytes) {
        None => None,
        Some((len, prefix_bytes)) => {
            let data_start = prefix_bytes as int;
            let data_end = data_start + len as int;
            if data_end > bytes.len() {
                None
            } else {
                Some(bytes.subrange(data_start, data_end))
            }
        }
    }
}

/// Proof: Vec<u8> SCALE encode/decode roundtrips
///
/// For any byte sequence v with len <= u32::MAX:
///   vec_u8_decode(vec_u8_encode(v)) == Some(v)
pub proof fn lemma_vec_u8_roundtrip(v: Seq<u8>)
    requires
        v.len() <= u32::MAX as int,
    ensures
        vec_u8_decode(vec_u8_encode(v)) == Some(v),
{
    let len = v.len() as u32;
    let encoded = vec_u8_encode(v);
    let compact_bytes = compact_encode(len);
    let compact_len = compact_encoded_len(len);

    // Step 1: compact encoding roundtrips
    lemma_compact_roundtrip(len);
    // Now: compact_decode(compact_encode(len)) == Some((len, compact_len))

    // Step 2: encoded = compact_bytes ++ v
    // compact_decode reads from the front, so it sees compact_bytes first
    assert(encoded =~= compact_bytes + v);

    // Step 3: compact_decode(encoded) succeeds because encoded starts with compact_bytes
    // We need to show that compact_decode(compact_bytes + v) == Some((len, compact_len))
    // This requires that compact_decode only looks at the first compact_len bytes
    lemma_compact_decode_prefix(len, v);

    // Step 4: after decoding the compact length, the remaining bytes are exactly v
    lemma_compact_encode_len(len);
    let prefix_bytes = compact_len;
    let data_start = prefix_bytes as int;
    let data_end = data_start + len as int;

    // data_end == compact_len + v.len() == encoded.len()
    assert(data_end <= encoded.len());

    // The subrange from data_start to data_end is exactly v
    assert(encoded.subrange(data_start, data_end) =~= v);
}

} // verus!
