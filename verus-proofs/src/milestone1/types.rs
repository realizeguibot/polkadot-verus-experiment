use vstd::prelude::*;

verus! {

// ============================================================================
// Concrete types for Milestone 1: validate_transaction
//
// These mirror actual Polkadot SDK types used in the validate_transaction
// call chain: Executive → System::initialize → validate dispatch.
// ============================================================================

/// Transaction source — where the transaction originated.
/// Mirrors: sp_runtime::transaction_validity::TransactionSource
pub enum TransactionSource {
    InBlock,
    Local,
    External,
}

/// Dispatch class — weight category for extrinsics.
/// Mirrors: frame_support::dispatch::DispatchClass
pub enum DispatchClass {
    Normal,
    Operational,
    Mandatory,
}

/// Pays fee flag.
/// Mirrors: frame_support::dispatch::Pays
pub enum Pays {
    Yes,
    No,
}

/// Dispatch info — metadata about a dispatchable call.
/// Mirrors: frame_support::dispatch::DispatchInfo
pub struct DispatchInfo {
    pub class: DispatchClass,
    pub pays_fee: Pays,
    pub weight_ref_time: u64,
    pub weight_proof_size: u64,
}

/// Transaction validity result types.
/// Mirrors: sp_runtime::transaction_validity
pub enum TransactionValidityError {
    Invalid(u8),   // InvalidTransaction variant index
    Unknown(u8),   // UnknownTransaction variant index
}

pub struct ValidTransaction {
    pub priority: u64,
    pub longevity: u64,
}

pub type TransactionValidityResult = Result<ValidTransaction, TransactionValidityError>;

/// Hash output type — 32 bytes (BlakeTwo256::Output for Polkadot).
pub type HashOutput = [u8; 32];

/// Digest item — simplified for validate_transaction context.
/// We only care about the encoded size contribution.
pub ghost enum DigestItem {
    PreRuntime([u8; 4], Seq<u8>),
    Consensus([u8; 4], Seq<u8>),
    Seal([u8; 4], Seq<u8>),
    Other(Seq<u8>),
    RuntimeEnvironmentUpdated,
}

/// Block header digest.
pub ghost struct Digest {
    pub logs: Seq<DigestItem>,
}

/// Block header.
pub ghost struct Header {
    pub parent_hash: HashOutput,
    pub number: u32,
    pub state_root: HashOutput,
    pub extrinsics_root: HashOutput,
    pub digest: Digest,
}

// ============================================================================
// System pallet state relevant to validate_transaction
// ============================================================================

/// Relevant System pallet storage items.
pub struct SystemState {
    /// Current block number in storage.
    pub block_number: u32,
    /// Maximum encoded header size from the runtime configuration.
    /// For Asset Hub this is ~5MB (5 * 1024 * 1024).
    pub max_header_size: u32,
}

// ============================================================================
// SCALE encoding overhead constants
//
// When validate_transaction calls System::initialize, it passes
// Default::default() as the digest, which is Digest { logs: vec![] }.
// SCALE encoding of this empty digest is a single compact-encoded 0 (1 byte).
//
// The base header overhead is:
//   parent_hash (32) + number (4) + state_root (32) + extrinsics_root (32) = 100
//   + compact-encoded digest length (1 byte for empty vec) = 101 bytes total
// ============================================================================

/// Base overhead of SCALE-encoded header excluding digest items.
/// parent_hash(32) + number(4) + state_root(32) + extrinsics_root(32) + compact_len(1) = 101
pub open spec fn base_header_overhead() -> u32 {
    101u32
}

/// Overhead of a Default::default() digest (empty logs vec).
/// SCALE encodes as: compact(0) = 1 byte, no items.
pub open spec fn default_digest_overhead() -> u32 {
    0u32  // The compact(0) is already counted in base_header_overhead
}

/// Total encoded size when validate_transaction calls System::initialize
/// with block_number+1 and Default::default() digest.
pub open spec fn validate_tx_header_overhead() -> u32 {
    // 32 (parent_hash) + 4 (number) + 32 (state_root) + 32 (extrinsics_root) + 1 (compact 0)
    (base_header_overhead()) as u32
}

} // verus!
