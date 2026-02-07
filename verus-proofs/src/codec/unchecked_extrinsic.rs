use vstd::prelude::*;
use crate::codec::compact::*;

verus! {

// ============================================================================
// SCALE encoding of UncheckedExtrinsic
//
// Source: polkadot-sdk/substrate/primitives/runtime/src/generic/unchecked_extrinsic.rs
//
// The encoding is:
//   compact_encode(payload.len() as u32) ++ payload
//
// where payload = preamble.encode() ++ call.encode()
//
// This is structurally identical to Vec<u8> encoding: a compact length prefix
// followed by an opaque byte payload. The difference is that the payload is
// structured (preamble + call), but for the roundtrip property of the outer
// encoding, the internal structure doesn't matter — only that:
//   encode_without_prefix(decode_payload(payload)) == payload
//
// We prove the roundtrip for the outer compact-length-prefixed structure,
// parameterized over an arbitrary payload encoding function.
//
// Asset Hub Polkadot type:
//   type UncheckedExtrinsic =
//       pallet_revive::evm::runtime::UncheckedExtrinsic<Address, Signature, EthExtraImpl>;
// ============================================================================

/// An UncheckedExtrinsic is modeled as its encoded payload bytes.
/// The actual type has fields (preamble, call) but for the outer encoding
/// roundtrip, all that matters is that encoding the fields produces the
/// same payload bytes, which we take as an axiom about the inner codec.
pub struct UncheckedExtrinsicModel {
    /// The payload = preamble.encode() ++ call.encode()
    pub ghost payload: Seq<u8>,
}

/// Encode an UncheckedExtrinsic: compact_len(payload.len()) ++ payload
/// This matches unchecked_extrinsic.rs lines 577-598:
///   fn encode(&self) -> Vec<u8> {
///       let tmp = self.encode_without_prefix();
///       let compact_len = Compact::<u32>(tmp.len() as u32);
///       compact_len.encode_to(&mut output);
///       output.extend(tmp);
///   }
pub open spec fn uxt_encode(uxt: UncheckedExtrinsicModel) -> Seq<u8>
    recommends uxt.payload.len() <= u32::MAX as int,
{
    compact_encode(uxt.payload.len() as u32) + uxt.payload
}

/// Decode an UncheckedExtrinsic from bytes.
/// This matches unchecked_extrinsic.rs lines 559-575:
///   fn decode(input) -> Result<Self, Error> {
///       let expected_length: Compact<u32> = Decode::decode(input)?;
///       Self::decode_with_len(input, expected_length.0 as usize)
///   }
///
/// decode_with_len reads exactly `expected_length` bytes as the payload,
/// then decodes preamble + call from that payload.
///
/// For the outer roundtrip, we just need to recover the payload bytes.
/// The inner decode (preamble + call from payload) is axiomatized.
pub open spec fn uxt_decode(bytes: Seq<u8>) -> Option<UncheckedExtrinsicModel> {
    match compact_decode(bytes) {
        None => None,
        Some((len, prefix_bytes)) => {
            let data_start = prefix_bytes as int;
            let data_end = data_start + len as int;
            if data_end > bytes.len() {
                None
            } else {
                Some(UncheckedExtrinsicModel {
                    payload: bytes.subrange(data_start, data_end),
                })
            }
        }
    }
}

/// Proof: UncheckedExtrinsic SCALE encode/decode roundtrips at the outer level.
///
/// For any UncheckedExtrinsic with payload.len() <= u32::MAX:
///   uxt_decode(uxt_encode(uxt)).payload == uxt.payload
///
/// This proves the compact-length-prefixed envelope roundtrips.
/// Combined with the axiom that inner codec roundtrips (preamble + call),
/// this gives full encode/decode roundtrip for UncheckedExtrinsic.
pub proof fn lemma_uxt_roundtrip(uxt: UncheckedExtrinsicModel)
    requires
        uxt.payload.len() <= u32::MAX as int,
    ensures
        uxt_decode(uxt_encode(uxt)) == Some(uxt),
{
    let payload = uxt.payload;
    let len = payload.len() as u32;
    let encoded = uxt_encode(uxt);
    let compact_bytes = compact_encode(len);
    let compact_len = compact_encoded_len(len);

    // Step 1: compact encoding roundtrips
    lemma_compact_roundtrip(len);

    // Step 2: encoded = compact_bytes ++ payload
    assert(encoded =~= compact_bytes + payload);

    // Step 3: compact_decode ignores trailing bytes (the payload)
    lemma_compact_decode_prefix(len, payload);

    // Step 4: after compact prefix, remaining bytes are exactly payload
    lemma_compact_encode_len(len);
    let prefix_bytes = compact_len;
    let data_start = prefix_bytes as int;
    let data_end = data_start + len as int;

    assert(data_end <= encoded.len());
    assert(encoded.subrange(data_start, data_end) =~= payload);

    // Step 5: reconstructed model equals original
    assert(UncheckedExtrinsicModel { payload: payload } == uxt);
}

} // verus!
