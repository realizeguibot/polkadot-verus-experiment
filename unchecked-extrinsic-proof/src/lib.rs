// Verus proof for UncheckedExtrinsic encode/decode roundtrip.
//
// This crate contains the REAL encode/decode implementations from sp-runtime's
// generic::UncheckedExtrinsic (polkadot-sdk), with minimal modifications for
// Verus compatibility:
//
// - Removed derive macros requiring parity-scale-codec-derive feature
//   (DecodeWithMemTracking implemented manually instead)
// - Removed non-encode/decode impls (TypeInfo, Debug, serde, Checkable, etc.)
// - Removed doc attributes (simple_mermaid, docify)
// - Added Verus annotations (requires/ensures) to encode/decode functions
//
// The encode/decode IMPLEMENTATIONS are verbatim from sp-runtime.
//
// Source: polkadot-sdk/substrate/primitives/runtime/src/generic/unchecked_extrinsic.rs

#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;
use codec::{
    Compact, CountedInput, Decode, DecodeWithMemLimit, DecodeWithMemTracking,
    Encode, EncodeLike, Input,
};
use vstd::prelude::*;

// ============================================================
// Type aliases and constants — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 52-76, 109-113
// ============================================================

/// Type to represent the version of the Extension.
pub type ExtensionVersion = u8;
/// Type to represent the extrinsic format version.
pub type ExtrinsicVersion = u8;

pub const EXTRINSIC_FORMAT_VERSION: ExtrinsicVersion = 5;
pub const LEGACY_EXTRINSIC_FORMAT_VERSION: ExtrinsicVersion = 4;
const EXTENSION_VERSION: ExtensionVersion = 0;
pub const DEFAULT_MAX_CALL_SIZE: usize = 16 * 1024 * 1024; // 16 MiB

const VERSION_MASK: u8 = 0b0011_1111;
const TYPE_MASK: u8 = 0b1100_0000;
const BARE_EXTRINSIC: u8 = 0b0000_0000;
const SIGNED_EXTRINSIC: u8 = 0b1000_0000;
const GENERAL_EXTRINSIC: u8 = 0b0100_0000;

// ============================================================
// Preamble enum — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 92-107
//
// Modification: replaced #[derive(DecodeWithMemTracking, Eq, PartialEq, Clone)]
// with #[derive(Eq, PartialEq, Clone)] + manual DecodeWithMemTracking impl
// (the derive macro requires the parity-scale-codec-derive feature which
// crashes the Verus compiler)
// ============================================================

#[derive(Eq, PartialEq, Clone)]
pub enum Preamble<Address, Signature, Extension> {
    Bare(ExtrinsicVersion),
    Signed(Address, Signature, Extension),
    General(ExtensionVersion, Extension),
}

impl<Address: DecodeWithMemTracking, Signature: DecodeWithMemTracking, Extension: DecodeWithMemTracking>
    DecodeWithMemTracking for Preamble<Address, Signature, Extension> {}

// ============================================================
// Preamble::Decode — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 115-148
// ============================================================

impl<Address, Signature, Extension> Decode for Preamble<Address, Signature, Extension>
where
    Address: Decode,
    Signature: Decode,
    Extension: Decode,
{
    fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
        let version_and_type = input.read_byte()?;

        let version = version_and_type & VERSION_MASK;
        let xt_type = version_and_type & TYPE_MASK;

        let preamble = match (version, xt_type) {
            (
                extrinsic_version @ LEGACY_EXTRINSIC_FORMAT_VERSION..=EXTRINSIC_FORMAT_VERSION,
                BARE_EXTRINSIC,
            ) => Self::Bare(extrinsic_version),
            (LEGACY_EXTRINSIC_FORMAT_VERSION, SIGNED_EXTRINSIC) => {
                let address = Address::decode(input)?;
                let signature = Signature::decode(input)?;
                let ext = Extension::decode(input)?;
                Self::Signed(address, signature, ext)
            },
            (EXTRINSIC_FORMAT_VERSION, GENERAL_EXTRINSIC) => {
                let ext_version = ExtensionVersion::decode(input)?;
                let ext = Extension::decode(input)?;
                Self::General(ext_version, ext)
            },
            (_, _) => return Err("Invalid transaction version".into()),
        };

        Ok(preamble)
    }
}

// ============================================================
// Preamble::Encode — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 150-189
// ============================================================

impl<Address, Signature, Extension> Encode for Preamble<Address, Signature, Extension>
where
    Address: Encode,
    Signature: Encode,
    Extension: Encode,
{
    fn size_hint(&self) -> usize {
        match &self {
            Preamble::Bare(_) => EXTRINSIC_FORMAT_VERSION.size_hint(),
            Preamble::Signed(address, signature, ext) => LEGACY_EXTRINSIC_FORMAT_VERSION
                .size_hint()
                .saturating_add(address.size_hint())
                .saturating_add(signature.size_hint())
                .saturating_add(ext.size_hint()),
            Preamble::General(ext_version, ext) => EXTRINSIC_FORMAT_VERSION
                .size_hint()
                .saturating_add(ext_version.size_hint())
                .saturating_add(ext.size_hint()),
        }
    }

    fn encode_to<T: codec::Output + ?Sized>(&self, dest: &mut T) {
        match &self {
            Preamble::Bare(extrinsic_version) => {
                (extrinsic_version | BARE_EXTRINSIC).encode_to(dest);
            },
            Preamble::Signed(address, signature, ext) => {
                (LEGACY_EXTRINSIC_FORMAT_VERSION | SIGNED_EXTRINSIC).encode_to(dest);
                address.encode_to(dest);
                signature.encode_to(dest);
                ext.encode_to(dest);
            },
            Preamble::General(ext_version, ext) => {
                (EXTRINSIC_FORMAT_VERSION | GENERAL_EXTRINSIC).encode_to(dest);
                ext_version.encode_to(dest);
                ext.encode_to(dest);
            },
        }
    }
}

// ============================================================
// UncheckedExtrinsic struct — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 246-266
//
// Modification: removed derive macros and codec attribute
// ============================================================

pub struct UncheckedExtrinsic<
    Address,
    Call,
    Signature,
    Extension,
    const MAX_CALL_SIZE: usize = DEFAULT_MAX_CALL_SIZE,
> {
    pub preamble: Preamble<Address, Signature, Extension>,
    pub function: Call,
    pub encoded_call: Option<Vec<u8>>,
}

// ============================================================
// UncheckedExtrinsic methods — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 331-451
//
// Included: new_bare, decode_with_len (with CloneBytes), encode_without_prefix
// Omitted: new_signed, new_transaction, from_parts (not needed for encode/decode)
// ============================================================

impl<Address, Call, Signature, Extension, const MAX_CALL_SIZE: usize>
    UncheckedExtrinsic<Address, Call, Signature, Extension, MAX_CALL_SIZE>
{
    pub fn new_bare(function: Call) -> Self {
        Self {
            preamble: Preamble::Bare(EXTRINSIC_FORMAT_VERSION),
            function,
            encoded_call: None,
        }
    }

    // Source: unchecked_extrinsic.rs lines 383-432 — verbatim
    fn decode_with_len<I: Input>(input: &mut I, len: usize) -> Result<Self, codec::Error>
    where
        Preamble<Address, Signature, Extension>: Decode,
        Call: DecodeWithMemTracking,
    {
        let mut input = CountedInput::new(input);

        let preamble = Decode::decode(&mut input)?;

        struct CloneBytes<'a, I>(&'a mut I, Vec<u8>);
        impl<I: Input> Input for CloneBytes<'_, I> {
            fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
                self.0.remaining_len()
            }

            fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
                self.0.read(into)?;

                self.1.extend_from_slice(into);
                Ok(())
            }

            fn descend_ref(&mut self) -> Result<(), codec::Error> {
                self.0.descend_ref()
            }

            fn ascend_ref(&mut self) {
                self.0.ascend_ref();
            }

            fn on_before_alloc_mem(&mut self, size: usize) -> Result<(), codec::Error> {
                self.0.on_before_alloc_mem(size)
            }
        }

        let mut clone_bytes = CloneBytes(&mut input, Vec::new());

        // Adds 1 byte to the `MAX_CALL_SIZE` as the decoding fails exactly at the given value and
        // the maximum should be allowed to fit in.
        let function =
            Call::decode_with_mem_limit(&mut clone_bytes, MAX_CALL_SIZE.saturating_add(1))?;

        let encoded_call = Some(clone_bytes.1);

        if input.count() != len as u64 {
            return Err("Invalid length prefix".into());
        }

        Ok(Self { preamble, function, encoded_call })
    }

    // Source: unchecked_extrinsic.rs lines 434-451 — verbatim
    fn encode_without_prefix(&self) -> Vec<u8>
    where
        Preamble<Address, Signature, Extension>: Encode,
        Call: Encode,
    {
        let mut encoded = self.preamble.encode();

        match &self.encoded_call {
            Some(call) => {
                encoded.extend(call);
            },
            None => {
                self.function.encode_to(&mut encoded);
            },
        }

        encoded
    }
}

// ============================================================
// UncheckedExtrinsic::Decode — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 566-582
// ============================================================

impl<Address, Call, Signature, Extension, const MAX_CALL_SIZE: usize> Decode
    for UncheckedExtrinsic<Address, Call, Signature, Extension, MAX_CALL_SIZE>
where
    Address: Decode,
    Signature: Decode,
    Call: DecodeWithMemTracking,
    Extension: Decode,
{
    fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
        // This is a little more complicated than usual since the binary format must be compatible
        // with SCALE's generic `Vec<u8>` type. Basically this just means accepting that there
        // will be a prefix of vector length.
        let expected_length: Compact<u32> = Decode::decode(input)?;

        Self::decode_with_len(input, expected_length.0 as usize)
    }
}

// ============================================================
// UncheckedExtrinsic::Encode — verbatim from sp-runtime
// Source: unchecked_extrinsic.rs lines 584-605
// ============================================================

impl<Address, Call, Signature, Extension> Encode
    for UncheckedExtrinsic<Address, Call, Signature, Extension>
where
    Preamble<Address, Signature, Extension>: Encode,
    Call: Encode,
    Extension: Encode,
{
    fn encode(&self) -> Vec<u8> {
        let tmp = self.encode_without_prefix();

        let compact_len = codec::Compact::<u32>(tmp.len() as u32);

        // Allocate the output buffer with the correct length
        let mut output = Vec::with_capacity(compact_len.size_hint() + tmp.len());

        compact_len.encode_to(&mut output);
        output.extend(tmp);

        output
    }
}

// ============================================================
// Verus specifications and roundtrip proofs
//
// The real encode/decode implementations above use generic trait dispatch
// which Verus cannot verify directly. We provide trusted specifications
// (external_body) for the concrete u8 instantiation, then PROVE that
// these specifications compose to give encode/decode roundtrip.
//
// What is PROVEN by Verus:
//   - The roundtrip composition: if encode produces bytes matching a
//     certain spec, and decode produces values matching a certain spec,
//     then encode(decode(x)) == x and decode(encode(x)) == x.
//
// What is TRUSTED (external_body):
//   - The per-function specs accurately describe the real encode/decode
//     behavior for u8 types. These specs are direct transcriptions of
//     the implementation logic above.
// ============================================================

verus! {

// --- Spec constants (Verus needs these as spec fns inside verus!) ---

pub open spec fn SPEC_EXTRINSIC_FORMAT_VERSION() -> u8 { 5 }
pub open spec fn SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION() -> u8 { 4 }
pub open spec fn SPEC_VERSION_MASK() -> u8 { 0x3Fu8 }
pub open spec fn SPEC_TYPE_MASK() -> u8 { 0xC0u8 }
pub open spec fn SPEC_BARE_EXTRINSIC() -> u8 { 0x00u8 }
pub open spec fn SPEC_SIGNED_EXTRINSIC() -> u8 { 0x80u8 }

// --- Trusted specifications for real encode/decode on concrete u8 types ---

/// Spec for UncheckedExtrinsic<u8,u8,u8,u8>::encode on a Bare preamble.
/// This directly describes the behavior of the real encode implementation above.
#[verifier::external_body]
pub fn encode_bare_u8_xt(version: u8, call: u8) -> (r: Vec<u8>)
    requires
        version >= SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION(),
        version <= SPEC_EXTRINSIC_FORMAT_VERSION(),
        version & SPEC_TYPE_MASK() == 0u8,
    ensures
        r@.len() == 3,
        r@[0] == (2u8 << 2u8),   // compact(2)
        r@[1] == (version | SPEC_BARE_EXTRINSIC()),
        r@[2] == call,
{
    let xt: UncheckedExtrinsic<u8, u8, u8, u8> = UncheckedExtrinsic {
        preamble: Preamble::Bare(version),
        function: call,
        encoded_call: None,
    };
    xt.encode()
}

/// Spec for UncheckedExtrinsic<u8,u8,u8,u8>::decode_all on a Bare extrinsic.
#[verifier::external_body]
pub fn decode_all_bare_u8_xt(data: &[u8]) -> (result: Result<(u8, u8), codec::Error>)
    ensures
        (data@.len() == 3
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 2
         && data@[1] & SPEC_TYPE_MASK() == SPEC_BARE_EXTRINSIC()
         && data@[1] & SPEC_VERSION_MASK() >= SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION()
         && data@[1] & SPEC_VERSION_MASK() <= SPEC_EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && (result.unwrap()).0 == data@[1] & SPEC_VERSION_MASK()
            && (result.unwrap()).1 == data@[2]
        ),
        result is Ok ==> (
            (result.unwrap()).0 >= SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION()
            && (result.unwrap()).0 <= SPEC_EXTRINSIC_FORMAT_VERSION()
            && (result.unwrap()).0 & SPEC_TYPE_MASK() == 0u8
        ),
{
    let xt = <UncheckedExtrinsic<u8, u8, u8, u8>>::decode(
        &mut &data[..]
    );
    match xt {
        Err(e) => Err(e),
        Ok(xt) => {
            match xt.preamble {
                Preamble::Bare(v) => Ok((v, xt.function)),
                _ => Err(codec::Error::from("Not a bare extrinsic")),
            }
        }
    }
}

/// Spec for UncheckedExtrinsic<u8,u8,u8,u8>::encode on a Signed preamble.
#[verifier::external_body]
pub fn encode_signed_u8_xt(addr: u8, sig: u8, ext: u8, call: u8) -> (r: Vec<u8>)
    ensures
        r@.len() == 6,
        r@[0] == (5u8 << 2u8),   // compact(5)
        r@[1] == (SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION() | SPEC_SIGNED_EXTRINSIC()),
        r@[2] == addr,
        r@[3] == sig,
        r@[4] == ext,
        r@[5] == call,
{
    let xt: UncheckedExtrinsic<u8, u8, u8, u8> = UncheckedExtrinsic {
        preamble: Preamble::Signed(addr, sig, ext),
        function: call,
        encoded_call: None,
    };
    xt.encode()
}

/// Spec for UncheckedExtrinsic<u8,u8,u8,u8>::decode_all on a Signed extrinsic.
#[verifier::external_body]
pub fn decode_all_signed_u8_xt(data: &[u8]) -> (result: Result<(u8, u8, u8, u8), codec::Error>)
    ensures
        (data@.len() == 6
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 5
         && data@[1] & SPEC_TYPE_MASK() == SPEC_SIGNED_EXTRINSIC()
         && data@[1] & SPEC_VERSION_MASK() == SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && (result.unwrap()).0 == data@[2]
            && (result.unwrap()).1 == data@[3]
            && (result.unwrap()).2 == data@[4]
            && (result.unwrap()).3 == data@[5]
        ),
{
    let xt = <UncheckedExtrinsic<u8, u8, u8, u8>>::decode(
        &mut &data[..]
    );
    match xt {
        Err(e) => Err(e),
        Ok(xt) => {
            match xt.preamble {
                Preamble::Signed(a, s, e) => Ok((a, s, e, xt.function)),
                _ => Err(codec::Error::from("Not a signed extrinsic")),
            }
        }
    }
}

// ===========================================================================
// PROVEN theorems — Verus verifies these compositions
// ===========================================================================

/// Theorem: Bare UncheckedExtrinsic encode-then-decode roundtrip.
///
/// For any valid extrinsic version (4 or 5) and any u8 call value,
/// encoding a Bare UncheckedExtrinsic and then decoding it recovers
/// the original version and call value.
pub fn theorem_bare_u8_encode_decode_roundtrip(version: u8, call: u8)
    -> (result: Result<(u8, u8), codec::Error>)
    requires
        version >= SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION(),
        version <= SPEC_EXTRINSIC_FORMAT_VERSION(),
        version & SPEC_TYPE_MASK() == 0u8,
    ensures
        result is Ok,
        (result.unwrap()).0 == version,
        (result.unwrap()).1 == call,
{
    let encoded = encode_bare_u8_xt(version, call);

    // Bitvector hints:
    assert((2u8 << 2u8) % 4u8 == 0u8) by(bit_vector);
    assert(((2u8 << 2u8) >> 2u8) == 2u8) by(bit_vector);
    assert(version & 0xC0u8 == 0u8 ==> version & 0x3Fu8 == version) by(bit_vector);
    assert((version | 0x00u8) & 0xC0u8 == version & 0xC0u8) by(bit_vector);
    assert((version | 0x00u8) & 0x3Fu8 == version & 0x3Fu8) by(bit_vector);


    decode_all_bare_u8_xt(encoded.as_slice())
}

/// Theorem: Bare UncheckedExtrinsic decode-then-encode roundtrip.
///
/// For any byte array, if it successfully decodes as a Bare
/// UncheckedExtrinsic with a u8 call (consuming all bytes),
/// then re-encoding produces the original byte array.
pub fn theorem_bare_u8_decode_encode_roundtrip(data: &[u8])
    -> (result: Result<Vec<u8>, codec::Error>)
    ensures
        (data@.len() == 3
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 2
         && data@[1] & SPEC_TYPE_MASK() == SPEC_BARE_EXTRINSIC()
         && data@[1] & SPEC_VERSION_MASK() >= SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION()
         && data@[1] & SPEC_VERSION_MASK() <= SPEC_EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && result.unwrap()@ =~= data@
        ),
{
    let decoded = decode_all_bare_u8_xt(data);
    match decoded {
        Err(e) => Err(e),
        Ok((version, call)) => {
            let re_encoded = encode_bare_u8_xt(version, call);

            assert(forall|b: u8| b % 4u8 == 0u8 && (b >> 2u8) == 2u8 ==> b == (2u8 << 2u8))
                by(bit_vector);
            assert(forall|b: u8| b & 0xC0u8 == 0u8 ==> b & 0x3Fu8 == b) by(bit_vector);
            assert(forall|b: u8| (b | 0x00u8) == b) by(bit_vector);

            Ok(re_encoded)
        },
    }
}

/// Theorem: Signed UncheckedExtrinsic encode-then-decode roundtrip.
///
/// For any u8 address, signature, extension, and call values,
/// encoding a Signed UncheckedExtrinsic and then decoding it recovers
/// the original values.
pub fn theorem_signed_u8_encode_decode_roundtrip(addr: u8, sig: u8, ext: u8, call: u8)
    -> (result: Result<(u8, u8, u8, u8), codec::Error>)
    ensures
        result is Ok,
        (result.unwrap()).0 == addr,
        (result.unwrap()).1 == sig,
        (result.unwrap()).2 == ext,
        (result.unwrap()).3 == call,
{
    let encoded = encode_signed_u8_xt(addr, sig, ext, call);

    assert((5u8 << 2u8) % 4u8 == 0u8) by(bit_vector);
    assert(((5u8 << 2u8) >> 2u8) == 5u8) by(bit_vector);
    assert((4u8 | 0x80u8) & 0xC0u8 == 0x80u8) by(bit_vector);
    assert((4u8 | 0x80u8) & 0x3Fu8 == 4u8) by(bit_vector);


    decode_all_signed_u8_xt(encoded.as_slice())
}

/// Theorem: Signed UncheckedExtrinsic decode-then-encode roundtrip.
///
/// For any byte array, if it successfully decodes as a Signed
/// UncheckedExtrinsic with u8 types (consuming all bytes),
/// then re-encoding produces the original byte array.
pub fn theorem_signed_u8_decode_encode_roundtrip(data: &[u8])
    -> (result: Result<Vec<u8>, codec::Error>)
    ensures
        (data@.len() == 6
         && data@[0] % 4 == 0
         && (data@[0] >> 2u8) == 5
         && data@[1] & SPEC_TYPE_MASK() == SPEC_SIGNED_EXTRINSIC()
         && data@[1] & SPEC_VERSION_MASK() == SPEC_LEGACY_EXTRINSIC_FORMAT_VERSION())
        ==> (
            result is Ok
            && result.unwrap()@ =~= data@
        ),
{
    let decoded = decode_all_signed_u8_xt(data);
    match decoded {
        Err(e) => Err(e),
        Ok((addr, sig, ext, call)) => {
            let re_encoded = encode_signed_u8_xt(addr, sig, ext, call);

            assert(forall|b: u8| b % 4u8 == 0u8 && (b >> 2u8) == 5u8 ==> b == (5u8 << 2u8))
                by(bit_vector);
            assert(forall|b: u8| b & 0xC0u8 == 0x80u8 && b & 0x3Fu8 == 4u8 ==> b == (4u8 | 0x80u8))
                by(bit_vector);

            Ok(re_encoded)
        },
    }
}

} // verus!
