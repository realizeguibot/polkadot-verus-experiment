use vstd::prelude::*;

verus! {

// ============================================================================
// Concrete types for Milestone 3: execute_block panic-freedom
//
// These mirror the actual runtime types used in the execute_block call
// chain, including Executive, System, Timestamp, and Aura pallets.
// ============================================================================

/// Hash output type — 32 bytes (BlakeTwo256::Output for Polkadot).
pub type HashOutput = [u8; 32];

/// Consensus engine identifier — 4-byte tag (e.g., b"aura").
pub type ConsensusEngineId = [u8; 4];

/// Digest item variants.
/// Mirrors: sp_runtime::generic::DigestItem
pub ghost enum DigestItem {
    PreRuntime(ConsensusEngineId, Seq<u8>),
    Consensus(ConsensusEngineId, Seq<u8>),
    Seal(ConsensusEngineId, Seq<u8>),
    Other(Seq<u8>),
    RuntimeEnvironmentUpdated,
}

impl DigestItem {
    pub open spec fn is_pre_runtime(&self) -> bool {
        self matches DigestItem::PreRuntime(..)
    }

    pub open spec fn is_seal(&self) -> bool {
        self matches DigestItem::Seal(..)
    }
}

/// Block header digest.
pub ghost struct Digest {
    pub logs: Seq<DigestItem>,
}

/// Block header.
/// Mirrors: sp_runtime::generic::Header<u32, BlakeTwo256>
pub ghost struct Header {
    pub parent_hash: HashOutput,
    pub number: u32,
    pub state_root: HashOutput,
    pub extrinsics_root: HashOutput,
    pub digest: Digest,
}

/// Extrinsic inclusion mode.
/// Mirrors: sp_runtime::ExtrinsicInclusionMode
pub ghost enum ExtrinsicInclusionMode {
    AllExtrinsics,
    OnlyInherents,
}

/// Model of a block extrinsic.
pub ghost struct Extrinsic {
    pub is_inherent: bool,
    pub dispatch_succeeds: bool,
    /// Whether the extrinsic decodes successfully from its encoded form.
    pub decodes_ok: bool,
}

/// Complete block.
pub ghost struct Block {
    pub header: Header,
    pub extrinsics: Seq<Extrinsic>,
}

/// Aura slot — u64.
pub type Slot = u64;

/// Timestamp — u64 milliseconds since Unix epoch.
pub type Moment = u64;

// ============================================================================
// Block helper specs
// ============================================================================

impl Block {
    pub open spec fn inherents_contiguous_with_boundary(&self, k: nat) -> bool {
        &&& k <= self.extrinsics.len()
        &&& (forall|i: int| 0 <= i < k ==> (#[trigger] self.extrinsics[i]).is_inherent)
        &&& (forall|i: int| k <= i < self.extrinsics.len() as int
                ==> !(#[trigger] self.extrinsics[i]).is_inherent)
    }

    pub open spec fn all_dispatches_succeed(&self) -> bool {
        forall|i: int| 0 <= i < self.extrinsics.len() as int
            ==> (#[trigger] self.extrinsics[i]).dispatch_succeeds
    }

    pub open spec fn all_extrinsics_decode_ok(&self) -> bool {
        forall|i: int| 0 <= i < self.extrinsics.len() as int
            ==> (#[trigger] self.extrinsics[i]).decodes_ok
    }

    pub open spec fn all_inherent(&self) -> bool {
        forall|i: int| 0 <= i < self.extrinsics.len() as int
            ==> (#[trigger] self.extrinsics[i]).is_inherent
    }
}

pub open spec fn is_only_inherents(mode: ExtrinsicInclusionMode) -> bool {
    match mode {
        ExtrinsicInclusionMode::OnlyInherents => true,
        ExtrinsicInclusionMode::AllExtrinsics => false,
    }
}

// ============================================================================
// Runtime state models
// ============================================================================

/// Relevant storage items for Aura pallet.
pub ghost struct AuraState {
    pub current_slot: Slot,
    pub slot_duration: Moment,
    /// Whether AllowMultipleBlocksPerSlot is enabled.
    pub allow_multiple_blocks_per_slot: bool,
}

/// Relevant storage items for Timestamp pallet.
pub ghost struct TimestampState {
    pub now: Moment,
    pub did_update: bool,
    pub min_period: Moment,
}

/// Aura inherent data extracted from the block's PreRuntime digest.
pub ghost struct AuraInherentData {
    pub slot: Slot,
}

/// Timestamp inherent data from the timestamp extrinsic.
pub ghost struct TimestampInherentData {
    pub timestamp: Moment,
}

// ============================================================================
// Oracle/uninterpreted functions (TCB)
// ============================================================================

/// Stored hash of block n.
pub uninterp spec fn stored_block_hash(n: u32) -> HashOutput;

/// The finalized header after executing all extrinsics and hooks.
pub uninterp spec fn finalized_header_after_execution(block: &Block) -> Header;

/// Whether multi-block migrations are ongoing.
pub uninterp spec fn multi_block_migration_ongoing(block: &Block) -> bool;

/// The inherent boundary index for a block.
pub uninterp spec fn inherent_boundary(block: &Block) -> nat;

/// Whether pallet hooks (other than Timestamp/Aura) complete without panic.
/// This is part of the TCB — we axiomatize it.
pub uninterp spec fn other_pallet_hooks_safe(block: &Block) -> bool;

/// Whether storage_root hash decoding succeeds.
/// This depends on the node using the same hash algorithm as the runtime.
pub uninterp spec fn storage_root_hash_decodable() -> bool;

/// Whether the aura author for the given slot is disabled.
pub uninterp spec fn aura_author_disabled(slot: Slot) -> bool;

// ============================================================================
// Block mode helper
// ============================================================================

pub open spec fn block_mode(block: &Block) -> ExtrinsicInclusionMode {
    if multi_block_migration_ongoing(block) {
        ExtrinsicInclusionMode::OnlyInherents
    } else {
        ExtrinsicInclusionMode::AllExtrinsics
    }
}

} // verus!
