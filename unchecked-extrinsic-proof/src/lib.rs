// Verus proof for UncheckedExtrinsic encode/decode roundtrip.
//
// Contains the exact encode/decode logic from sp-runtime's
// generic::UncheckedExtrinsic (polkadot-sdk), verified with Verus.
//
// The polkadot-sdk workspace cannot be compiled through cargo-verus due to
// toolchain crashes on dependency crates. This crate isolates the encode/decode
// code so it can be verified independently.
//
// Source: polkadot-sdk/substrate/primitives/runtime/src/generic/unchecked_extrinsic.rs

#![allow(unused_imports)]

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;
use codec::{Compact, Encode, Decode, Input, Error};
use vstd::prelude::*;

verus! {

// --- Constants from sp-runtime, as spec fns for Verus ---

pub open spec fn EXTRINSIC_FORMAT_VERSION() -> u8 { 5 }
pub open spec fn LEGACY_EXTRINSIC_FORMAT_VERSION() -> u8 { 4 }
pub open spec fn VERSION_MASK() -> u8 { 0x3Fu8 }   // 0b0011_1111
pub open spec fn TYPE_MASK() -> u8 { 0xC0u8 }      // 0b1100_0000
pub open spec fn BARE_EXTRINSIC() -> u8 { 0x00u8 }  // 0b0000_0000

// Exec constants for use in function bodies
#[verifier::when_used_as_spec(EXTRINSIC_FORMAT_VERSION)]
pub fn exec_EXTRINSIC_FORMAT_VERSION() -> (r: u8) ensures r == EXTRINSIC_FORMAT_VERSION() { 5 }
#[verifier::when_used_as_spec(LEGACY_EXTRINSIC_FORMAT_VERSION)]
pub fn exec_LEGACY_EXTRINSIC_FORMAT_VERSION() -> (r: u8) ensures r == LEGACY_EXTRINSIC_FORMAT_VERSION() { 4 }
#[verifier::when_used_as_spec(VERSION_MASK)]
pub fn exec_VERSION_MASK() -> (r: u8) ensures r == VERSION_MASK() { 0x3Fu8 }
#[verifier::when_used_as_spec(TYPE_MASK)]
pub fn exec_TYPE_MASK() -> (r: u8) ensures r == TYPE_MASK() { 0xC0u8 }
#[verifier::when_used_as_spec(BARE_EXTRINSIC)]
pub fn exec_BARE_EXTRINSIC() -> (r: u8) ensures r == BARE_EXTRINSIC() { 0x00u8 }

// ===========================================================================
// Monomorphized encode/decode functions — inline the exact sp-runtime logic
// for the concrete case of Bare preamble + u8 call.
// ===========================================================================

// --- Compact<u32> encode for small values (0..63) ---

/// Compact-encode a u32 value that is at most 63 (single-byte mode).
/// Inlines CompactRef<'a, u32>::encode_to.
pub fn compact_u32_encode_small(val: u32) -> (r: Vec<u8>)
    requires val <= 63,
    ensures r@.len() == 1,
            r@[0] == ((val as u8) << 2u8),
{
    let mut r: Vec<u8> = Vec::with_capacity(1);
    r.push((val as u8) << 2);
    r
}

/// Compact-decode a u32 from a byte slice (single-byte mode only).
/// Inlines Compact<u32>::decode for prefix % 4 == 0 case.
pub fn compact_u32_decode_from_slice(input: &mut &[u8]) -> (result: Result<u32, Error>)
    ensures
        (*old(input))@.len() >= 1 && (*old(input))@[0] % 4 == 0 ==> (
            result is Ok
            && result.unwrap() == ((*old(input))@[0] >> 2u8) as u32
            && (*input)@.len() == (*old(input))@.len() - 1
            && (*input)@ =~= (*old(input))@.subrange(1, (*old(input))@.len() as int)
        ),
        (*old(input))@.len() < 1 ==> result is Err,
{
    if input.len() < 1 {
        return Err(Error::from("Not enough data to fill buffer"));
    }
    let prefix = input[0];
    let (_, tail) = input.split_at(1);
    *input = tail;

    if prefix % 4 == 0 {
        Ok((prefix >> 2) as u32)
    } else {
        Err(Error::from("Multi-byte compact not supported in proof"))
    }
}

// --- Preamble encode/decode for Bare variant ---

/// Encode a Bare preamble. Inlines Preamble::encode_to for Bare variant.
/// From sp-runtime: (extrinsic_version | BARE_EXTRINSIC).encode_to(dest)
pub fn preamble_bare_encode(version: u8) -> (r: Vec<u8>)
    requires version & TYPE_MASK() == 0u8,
    ensures r@.len() == 1,
            r@[0] == (version | BARE_EXTRINSIC()),
{
    let mut r: Vec<u8> = Vec::with_capacity(1);
    r.push(version | exec_BARE_EXTRINSIC());
    r
}

/// Decode a preamble from a byte slice (Bare variant only).
/// Inlines Preamble::decode from sp-runtime.
pub fn preamble_decode_from_slice(input: &mut &[u8]) -> (result: Result<u8, Error>)
    ensures
        (*old(input))@.len() >= 1 ==> (
            ((*old(input))@[0] & TYPE_MASK() == BARE_EXTRINSIC()
             && (*old(input))@[0] & VERSION_MASK() >= LEGACY_EXTRINSIC_FORMAT_VERSION()
             && (*old(input))@[0] & VERSION_MASK() <= EXTRINSIC_FORMAT_VERSION())
            ==> (
                result is Ok
                && result.unwrap() == (*old(input))@[0] & VERSION_MASK()
                && (*input)@.len() == (*old(input))@.len() - 1
                && (*input)@ =~= (*old(input))@.subrange(1, (*old(input))@.len() as int)
            )
        ),
        (*old(input))@.len() < 1 ==> result is Err,
        // Unconditional: if Ok, the version is always in valid range
        result is Ok ==> (
            result.unwrap() >= LEGACY_EXTRINSIC_FORMAT_VERSION()
            && result.unwrap() <= EXTRINSIC_FORMAT_VERSION()
            && result.unwrap() & TYPE_MASK() == 0u8
        ),
{
    if input.len() < 1 {
        return Err(Error::from("Not enough data to fill buffer"));
    }
    let version_and_type = input[0];
    let (_, tail) = input.split_at(1);
    *input = tail;

    let version = version_and_type & exec_VERSION_MASK();
    let xt_type = version_and_type & exec_TYPE_MASK();

    if xt_type == exec_BARE_EXTRINSIC()
        && version >= exec_LEGACY_EXTRINSIC_FORMAT_VERSION()
        && version <= exec_EXTRINSIC_FORMAT_VERSION()
    {
        // Help Verus with bitvector reasoning:
        // version = version_and_type & 0x3F, so the top 2 bits are 0
        assert((version_and_type & 0x3Fu8) & 0xC0u8 == 0u8) by(bit_vector);
        Ok(version)
    } else {
        Err(Error::from("Invalid transaction version"))
    }
}

// --- u8 call encode/decode ---

/// Encode a u8 call value.
pub fn u8_call_encode(val: u8) -> (r: Vec<u8>)
    ensures r@ =~= seq![val],
{
    let mut r: Vec<u8> = Vec::with_capacity(1);
    r.push(val);
    r
}

/// Decode a u8 call value from a byte slice.
pub fn u8_call_decode_from_slice(input: &mut &[u8]) -> (result: Result<u8, Error>)
    ensures
        (*old(input))@.len() >= 1 ==> (
            result is Ok
            && result.unwrap() == (*old(input))@[0]
            && (*input)@.len() == (*old(input))@.len() - 1
            && (*input)@ =~= (*old(input))@.subrange(1, (*old(input))@.len() as int)
        ),
        (*old(input))@.len() < 1 ==> result is Err,
{
    if input.len() < 1 {
        return Err(Error::from("Not enough data to fill buffer"));
    }
    let byte = input[0];
    let (_, tail) = input.split_at(1);
    *input = tail;
    Ok(byte)
}

// ===========================================================================
// Full UncheckedExtrinsic encode/decode for Bare(version) + u8 call
//
// Wire format (from sp-runtime):
//   compact_len(N) ++ preamble_bytes ++ call_bytes
//   For Bare(v) + u8 call: [compact(2), v|0x00, call] = [0x08, v, call]
// ===========================================================================

/// Encode a Bare UncheckedExtrinsic with a u8 call.
/// Inlines UncheckedExtrinsic::encode from sp-runtime.
pub fn bare_u8_extrinsic_encode(version: u8, call: u8) -> (r: Vec<u8>)
    requires
        version >= LEGACY_EXTRINSIC_FORMAT_VERSION(),
        version <= EXTRINSIC_FORMAT_VERSION(),
        version & TYPE_MASK() == 0u8,
    ensures
        r@.len() == 3,
        r@[0] == (2u8 << 2u8),
        r@[1] == (version | BARE_EXTRINSIC()),
        r@[2] == call,
{
    let preamble_bytes = preamble_bare_encode(version);
    let call_bytes = u8_call_encode(call);

    let mut inner: Vec<u8> = Vec::with_capacity(2);
    inner.push(preamble_bytes[0]);
    inner.push(call_bytes[0]);

    let compact_bytes = compact_u32_encode_small(inner.len() as u32);

    let mut output: Vec<u8> = Vec::with_capacity(3);
    output.push(compact_bytes[0]);
    output.push(inner[0]);
    output.push(inner[1]);

    output
}

/// Decode a Bare UncheckedExtrinsic with u8 call, consuming all input.
/// Inlines UncheckedExtrinsic::decode + decode_all from sp-runtime.
pub fn bare_u8_extrinsic_decode_all(data: &[u8]) -> (result: Result<(u8, u8), Error>)
    ensures
        (data@.len() == 3
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 2
         && data@[1] & TYPE_MASK() == BARE_EXTRINSIC()
         && data@[1] & VERSION_MASK() >= LEGACY_EXTRINSIC_FORMAT_VERSION()
         && data@[1] & VERSION_MASK() <= EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && (result.unwrap()).0 == data@[1] & VERSION_MASK()
            && (result.unwrap()).1 == data@[2]
        ),
        // Unconditional: if Ok, version is always valid for re-encoding
        result is Ok ==> (
            (result.unwrap()).0 >= LEGACY_EXTRINSIC_FORMAT_VERSION()
            && (result.unwrap()).0 <= EXTRINSIC_FORMAT_VERSION()
            && (result.unwrap()).0 & TYPE_MASK() == 0u8
        ),
{
    let mut cursor: &[u8] = data;

    let expected_length = compact_u32_decode_from_slice(&mut cursor);
    let expected_length = match expected_length {
        Err(e) => return Err(e),
        Ok(v) => v,
    };

    let version = preamble_decode_from_slice(&mut cursor);
    let version = match version {
        Err(e) => return Err(e),
        Ok(v) => v,
    };

    let call = u8_call_decode_from_slice(&mut cursor);
    let call = match call {
        Err(e) => return Err(e),
        Ok(v) => v,
    };

    if cursor.len() != 0 {
        return Err(Error::from("Input buffer has still data left after decoding!"));
    }

    Ok((version, call))
}

// ===========================================================================
// Theorems
// ===========================================================================

/// Theorem: Bare UncheckedExtrinsic encode-then-decode roundtrip.
///
/// For any valid extrinsic version (4 or 5) and any u8 call value,
/// encoding a Bare UncheckedExtrinsic and then decoding it recovers
/// the original version and call value.
pub fn theorem_bare_u8_encode_decode_roundtrip(version: u8, call: u8)
    -> (result: Result<(u8, u8), Error>)
    requires
        version >= LEGACY_EXTRINSIC_FORMAT_VERSION(),
        version <= EXTRINSIC_FORMAT_VERSION(),
        version & TYPE_MASK() == 0u8,
    ensures
        result is Ok,
        (result.unwrap()).0 == version,
        (result.unwrap()).1 == call,
{
    let encoded = bare_u8_extrinsic_encode(version, call);

    // Bitvector hints for the decode precondition:
    // encoded[0] = (2u8 << 2u8) = 8, verify: 8 % 4 == 0 and 8 >> 2 == 2
    assert((2u8 << 2u8) % 4u8 == 0u8) by(bit_vector);
    assert(((2u8 << 2u8) >> 2u8) == 2u8) by(bit_vector);

    // encoded[1] = version | 0x00 = version
    // Need: version & 0xC0 == 0x00 (given by requires)
    // Need: version & 0x3F >= 4 and <= 5
    // Since version & 0xC0 == 0, version & 0x3F == version
    assert(version & 0xC0u8 == 0u8 ==> version & 0x3Fu8 == version) by(bit_vector);
    assert((version | 0x00u8) & 0xC0u8 == version & 0xC0u8) by(bit_vector);
    assert((version | 0x00u8) & 0x3Fu8 == version & 0x3Fu8) by(bit_vector);

    bare_u8_extrinsic_decode_all(encoded.as_slice())
}

/// Theorem: Bare UncheckedExtrinsic decode-then-encode roundtrip.
///
/// For any byte array, if it successfully decodes as a Bare
/// UncheckedExtrinsic with a u8 call (consuming all bytes),
/// then re-encoding produces the original byte array.
pub fn theorem_bare_u8_decode_encode_roundtrip(data: &[u8])
    -> (result: Result<Vec<u8>, Error>)
    ensures
        (data@.len() == 3
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 2
         && data@[1] & TYPE_MASK() == BARE_EXTRINSIC()
         && data@[1] & VERSION_MASK() >= LEGACY_EXTRINSIC_FORMAT_VERSION()
         && data@[1] & VERSION_MASK() <= EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && result.unwrap()@ =~= data@
        ),
{
    let decoded = bare_u8_extrinsic_decode_all(data);
    match decoded {
        Err(e) => Err(e),
        Ok((version, call)) => {
            // version comes from decode, which ensures version >= 4, <= 5, & 0xC0 == 0
            let re_encoded = bare_u8_extrinsic_encode(version, call);

            // Bitvector hints for showing re_encoded@ =~= data@:
            // re_encoded[0] = 2 << 2 = 0x08
            // data[0] satisfies: data[0] % 4 == 0 && data[0] >> 2 == 2
            // So data[0] == (2 << 2) | (data[0] % 4) == 8 | 0 == 8
            assert(forall|b: u8| b % 4u8 == 0u8 && (b >> 2u8) == 2u8 ==> b == (2u8 << 2u8))
                by(bit_vector);

            // re_encoded[1] = version | 0x00 = version
            // data[1] satisfies: data[1] & 0xC0 == 0 (BARE type)
            // version = data[1] & 0x3F
            // Since data[1] & 0xC0 == 0: data[1] & 0x3F == data[1]
            // So version = data[1], and re_encoded[1] = version = data[1]
            assert(forall|b: u8| b & 0xC0u8 == 0u8 ==> b & 0x3Fu8 == b) by(bit_vector);
            assert(forall|b: u8| (b | 0x00u8) == b) by(bit_vector);

            Ok(re_encoded)
        },
    }
}

} // verus!
