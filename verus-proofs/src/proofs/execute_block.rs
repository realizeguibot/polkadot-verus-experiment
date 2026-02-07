use vstd::prelude::*;
use crate::model_digest::*;
use crate::model_header::*;
use crate::proofs::final_checks::*;
use crate::proofs::apply_extrinsics::*;

verus! {

// ============================================================================
// EXTERNAL_BODY TRUSTED SPECIFICATIONS
//
// These model the behavior of components outside our verification scope.
// Each one is an axiom that becomes part of the Trusted Computing Base (TCB).
// ============================================================================

/// Pallet hooks (on_initialize, on_finalize, on_idle, PostTransactions, etc.)
/// We assume they do not panic.
///
/// TCB justification: These hooks are tested extensively in the Polkadot SDK
/// test suite. A full verification would require modeling each of the 40+
/// pallets individually.
pub uninterp spec fn pallet_hooks_do_not_panic(block: &Block) -> bool;

/// The block number is greater than zero.
/// Genesis block (number 0) is never executed via execute_block.
pub open spec fn block_number_positive(block: &Block) -> bool {
    block.header.number > 0u32
}

/// The parent hash in the header matches the stored hash of the previous block.
pub uninterp spec fn parent_hash_valid(block: &Block) -> bool;

/// Multi-block migrations are not ongoing (normal mode).
/// When MBMs are ongoing, mode is OnlyInherents — handled separately.
pub uninterp spec fn multi_block_migration_ongoing(block: &Block) -> bool;

/// The extrinsic inclusion mode for this block.
pub open spec fn block_mode(block: &Block) -> ExtrinsicInclusionMode {
    if multi_block_migration_ongoing(block) {
        ExtrinsicInclusionMode::OnlyInherents
    } else {
        ExtrinsicInclusionMode::AllExtrinsics
    }
}

// ============================================================================
// THE "CORRECT DIGESTS" PRECONDITION
//
// This is the formal statement of what "correct digests" means.
// A block satisfies this when it was produced by an honest block builder
// and the header is consistent with execution.
// ============================================================================

pub open spec fn correct_digests(block: &Block) -> bool {
    let finalized = finalized_header_after_execution(block);
    &&& block.header.digest == finalized.digest
    &&& block.header.state_root == finalized.state_root
    &&& block.header.extrinsics_root == finalized.extrinsics_root
}

pub open spec fn well_formed_block(block: &Block) -> bool {
    let mode = block_mode(block);
    &&& block.well_formed(mode)
    &&& block_number_positive(block)
    &&& parent_hash_valid(block)
    &&& correct_digests(block)
}

// ============================================================================
// MAIN THEOREM
// ============================================================================

/// **THEOREM: The Asset Hub STF does not panic given correct digests.**
///
/// Formally: for any block satisfying the `well_formed_block` precondition,
/// the modeled `execute_block` function completes without panic.
///
/// The proof composes:
///   1. `initial_checks` — no panic (parent hash valid)
///   2. `apply_extrinsics` — no panic (well-formed block)
///   3. `final_checks` — no panic (correct digests)
///
/// Pallet hooks (on_initialize, on_finalize, on_idle) are part of the TCB.
proof fn theorem_execute_block_no_panic(block: Block)
    requires
        well_formed_block(&block),
{
    let mode = block_mode(&block);
    let k = block.inherent_boundary();

    // --- Step 1: initial_checks does not panic ---
    // The header number > 0 and parent hash matches stored hash.
    // (modeled in final_checks.rs::initial_checks_no_panic)
    assert(block.header.number > 0u32);

    // --- Step 2: apply_extrinsics does not panic ---
    // The block is well-formed: inherents contiguous, all dispatches succeed,
    // OnlyInherents mode → all inherents.
    //
    // We need to establish the forall preconditions from the well_formed spec.
    // block.well_formed(mode) gives us inherents_contiguous_at_start() etc.
    //
    // From inherents_contiguous_at_start, we get the boundary k.
    assert(block.inherents_contiguous_at_start());
    assert(block.inherents_contiguous_with_boundary(k));
    assert(k <= block.extrinsics.len());
    assert(block.all_dispatches_succeed());

    // If mode is OnlyInherents, all extrinsics are inherents (k == len)
    if is_only_inherents(mode) {
        // From well_formed: all extrinsics are inherents
        // Combined with contiguous_with_boundary: k == len
        assert(forall|i: int| 0 <= i < block.extrinsics.len() as int
            ==> (#[trigger] block.extrinsics[i]).is_inherent);
        // Since all are inherents and boundary says non-inherents start at k,
        // k must equal len.
        lemma_all_inherent_means_k_is_len(block.extrinsics, k);
    }

    theorem_apply_extrinsics_no_panic(mode, block.extrinsics, k);

    // --- Step 3: final_checks does not panic ---
    // The correct_digests precondition ensures header matches finalized header.
    let finalized = finalized_header_after_execution(&block);
    assert(block.header.digest == finalized.digest);
    assert(block.header.state_root == finalized.state_root);
    assert(block.header.extrinsics_root == finalized.extrinsics_root);

    // Digest logs equality implies pointwise equality.
    assert(block.header.digest.logs =~= finalized.digest.logs);
    assert(block.header.digest.logs.len() == finalized.digest.logs.len());

    assert forall|i: int|
        0 <= i < block.header.digest.logs.len()
    implies
        (#[trigger] block.header.digest.logs[i]) == finalized.digest.logs[i]
    by {
        // From extensional equality of the sequences
    }

    final_checks_no_panic(block.header, finalized);
}

/// Helper lemma: if all extrinsics are inherents and the boundary property holds,
/// then k equals the total number of extrinsics.
proof fn lemma_all_inherent_means_k_is_len(
    extrinsics: Seq<Extrinsic>,
    k: nat,
)
    requires
        k <= extrinsics.len(),
        forall|i: int| 0 <= i < k ==> (#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| k <= i < extrinsics.len() as int
            ==> !(#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).is_inherent,
    ensures
        k == extrinsics.len(),
{
    // Proof by contradiction: if k < len, then extrinsics[k] is both
    // inherent (from the third forall) and not inherent (from the second forall).
    if k < extrinsics.len() {
        assert(extrinsics[k as int].is_inherent);     // third forall
        assert(!extrinsics[k as int].is_inherent);    // second forall
        // Contradiction.
    }
}

} // verus!
