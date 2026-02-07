use vstd::prelude::*;
use crate::milestone3::types::*;

verus! {

// ============================================================================
// Executive::apply_extrinsics — ported from executive/src/lib.rs:749-783
//
// Panic points covered:
//   #4: Extrinsic decode failure
//   #5: Inherent after non-inherent
//   #6: Non-inherent in OnlyInherents mode
//   #7: apply_extrinsics returns Err (implies execute_block assert fails)
//
// The real code:
//
// fn apply_extrinsics(block: &Block) -> Result<ExtrinsicInclusionMode, ...> {
//     let mut first_non_inherent_idx = 0;
//     for (idx, maybe_uxt) in block.extrinsics().iter().enumerate() {
//         let encoded = maybe_uxt.encode();
//         let uxt = Unchecked::decode_all_with_depth_limit(...)
//             .map_err(|_| InvalidTransaction::Call)?;        // #4
//         let is_inherent = uxt.is_inherent();
//         if is_inherent {
//             ensure!(first_non_inherent_idx == idx, ...);    // #5
//             first_non_inherent_idx = idx + 1;
//         } else {
//             ensure!(mode != OnlyInherents, ...);            // #6
//         }
//         let _ = uxt.apply(info)?;                          // dispatch
//     }
//     Ok(mode)
// }
//
// Then execute_block checks:
//   let res = apply_extrinsics(&block);
//   assert!(res.is_ok(), "...");                              // #7
// ============================================================================

/// Error type for apply_extrinsics.
pub ghost enum ApplyError {
    DecodeError(nat),
    InvalidInherentPosition(nat),
    OnlyInherentsAllowed(nat),
    DispatchError(nat),
}

pub type ApplyResult = Result<(), ApplyError>;

/// Recursive spec modeling the apply_extrinsics loop.
pub open spec fn apply_extrinsics_spec(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    idx: nat,
    first_non_inherent_idx: nat,
) -> ApplyResult
    decreases extrinsics.len() - idx,
{
    if idx >= extrinsics.len() {
        Ok(())
    } else {
        let ext = extrinsics[idx as int];

        // Step 1: decode check
        if !ext.decodes_ok {
            Err(ApplyError::DecodeError(idx))
        } else if ext.is_inherent {
            // Inherent: check position
            if first_non_inherent_idx != idx {
                Err(ApplyError::InvalidInherentPosition(idx))
            } else if !ext.dispatch_succeeds {
                Err(ApplyError::DispatchError(idx))
            } else {
                apply_extrinsics_spec(mode, extrinsics, idx + 1, first_non_inherent_idx + 1)
            }
        } else {
            // Non-inherent
            if is_only_inherents(mode) {
                Err(ApplyError::OnlyInherentsAllowed(idx))
            } else if !ext.dispatch_succeeds {
                Err(ApplyError::DispatchError(idx))
            } else {
                apply_extrinsics_spec(mode, extrinsics, idx + 1, first_non_inherent_idx)
            }
        }
    }
}

/// **THEOREM: apply_extrinsics returns Ok for a well-formed block.**
///
/// Preconditions:
///   - All extrinsics decode successfully
///   - Inherents are contiguous at the start (boundary at k)
///   - All dispatches succeed
///   - OnlyInherents mode ⟹ k == len (all inherent)
pub proof fn theorem_apply_extrinsics_no_panic(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    k: nat,
)
    requires
        k <= extrinsics.len(),
        forall|i: int| 0 <= i < k ==> (#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| k <= i < extrinsics.len() as int
            ==> !(#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).dispatch_succeeds,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).decodes_ok,
        is_only_inherents(mode) ==> k == extrinsics.len(),
    ensures
        apply_extrinsics_spec(mode, extrinsics, 0, 0) is Ok,
{
    lemma_inherent_phase(mode, extrinsics, k, 0);
}

/// Inherent phase: indices 0..k. Invariant: first_non_inherent_idx == pos.
proof fn lemma_inherent_phase(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    k: nat,
    pos: nat,
)
    requires
        k <= extrinsics.len(),
        forall|i: int| 0 <= i < k ==> (#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| k <= i < extrinsics.len() as int
            ==> !(#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).dispatch_succeeds,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).decodes_ok,
        is_only_inherents(mode) ==> k == extrinsics.len(),
        pos <= k,
    ensures
        apply_extrinsics_spec(mode, extrinsics, pos, pos) is Ok,
    decreases extrinsics.len() - pos,
{
    reveal(apply_extrinsics_spec);

    if pos >= extrinsics.len() {
        // Past end → Ok
    } else if pos < k {
        let ext = extrinsics[pos as int];
        assert(ext.is_inherent);
        assert(ext.decodes_ok);
        assert(ext.dispatch_succeeds);
        lemma_inherent_phase(mode, extrinsics, k, pos + 1);
    } else {
        // pos == k
        assert(pos == k);
        if is_only_inherents(mode) {
            assert(k == extrinsics.len());
        } else {
            lemma_noninherent_phase(mode, extrinsics, k, pos);
        }
    }
}

/// Non-inherent phase: indices k..len. first_non_inherent_idx frozen at k.
proof fn lemma_noninherent_phase(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    k: nat,
    pos: nat,
)
    requires
        k <= extrinsics.len(),
        forall|i: int| k <= i < extrinsics.len() as int
            ==> !(#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).dispatch_succeeds,
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).decodes_ok,
        !is_only_inherents(mode),
        pos >= k,
        pos <= extrinsics.len(),
    ensures
        apply_extrinsics_spec(mode, extrinsics, pos, k) is Ok,
    decreases extrinsics.len() - pos,
{
    reveal(apply_extrinsics_spec);

    if pos >= extrinsics.len() {
        // Past end → Ok
    } else {
        let ext = extrinsics[pos as int];
        assert(!ext.is_inherent);
        assert(ext.decodes_ok);
        assert(ext.dispatch_succeeds);
        assert(!is_only_inherents(mode));
        lemma_noninherent_phase(mode, extrinsics, k, pos + 1);
    }
}

/// Helper: if all extrinsics are inherents and boundary is k, then k == len.
pub proof fn lemma_all_inherent_means_k_is_len(
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
    if k < extrinsics.len() {
        assert(extrinsics[k as int].is_inherent);
        assert(!extrinsics[k as int].is_inherent);
    }
}

} // verus!
