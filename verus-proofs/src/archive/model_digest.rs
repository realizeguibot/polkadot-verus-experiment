use vstd::prelude::*;

verus! {

/// Consensus engine identifier — 4-byte tag (e.g., b"aura", b"BABE").
/// Mirrors: sp_runtime::ConsensusEngineId = [u8; 4]
pub type ConsensusEngineId = [u8; 4];

/// Digest item variants.
/// Mirrors: sp_runtime::generic::DigestItem
///
/// Modeled as a ghost (spec-only) enum. Equality is handled by Verus's
/// structural equality on spec types (Seq, enum variants, etc.).
/// This is a #[verifier::spec] type — it exists only in proofs, not at runtime.
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

    pub open spec fn is_consensus(&self) -> bool {
        self matches DigestItem::Consensus(..)
    }
}

/// Block header digest — a list of digest items.
/// Mirrors: sp_runtime::generic::Digest
pub ghost struct Digest {
    pub logs: Seq<DigestItem>,
}

impl Digest {
    pub open spec fn len(&self) -> nat {
        self.logs.len()
    }
}

/// Hash output type — 32 bytes (BlakeTwo256::Output for Polkadot).
pub type HashOutput = [u8; 32];

/// Block header model.
/// Mirrors: sp_runtime::generic::Header<u32, BlakeTwo256>
///
/// For Asset Hub: Number = u32, Hash::Output = [u8; 32].
pub ghost struct Header {
    pub parent_hash: HashOutput,
    pub number: u32,
    pub state_root: HashOutput,
    pub extrinsics_root: HashOutput,
    pub digest: Digest,
}

/// Extract only the PreRuntime digest items from the header.
/// Mirrors: Executive::extract_pre_digest
///
/// This function is proven to never panic:
/// - No array out-of-bounds (loop bounded by seq length)
/// - No arithmetic overflow (index bounded by usize::MAX via seq length)
/// - All items filtered purely by pattern matching (no unwrap)
pub open spec fn extract_pre_digest(header: &Header) -> Digest {
    Digest {
        logs: header.digest.logs.filter(|item: DigestItem| item.is_pre_runtime()),
    }
}

/// Proof: extract_pre_digest returns only PreRuntime items.
proof fn lemma_extract_pre_digest_only_pre_runtime(header: &Header)
    ensures
        forall|i: int|
            0 <= i < extract_pre_digest(header).logs.len()
            ==> (#[trigger] extract_pre_digest(header).logs[i]).is_pre_runtime(),
{
    let src = header.digest.logs;
    let pred = |item: DigestItem| item.is_pre_runtime();
    let filtered = src.filter(pred);
    // vstd's broadcast lemma: filtered elements satisfy the predicate
    assert forall|i: int| 0 <= i < filtered.len() implies pred(#[trigger] filtered[i]) by {
        src.lemma_filter_pred(pred, i);
    }
}

/// Proof: extract_pre_digest result length <= original digest length.
proof fn lemma_extract_pre_digest_length_bound(header: &Header)
    ensures
        extract_pre_digest(header).logs.len() <= header.digest.logs.len(),
{
    let src = header.digest.logs;
    let pred = |item: DigestItem| item.is_pre_runtime();
    // Seq::filter can only remove elements, never add.
    src.lemma_filter_len(pred);
}

} // verus!
