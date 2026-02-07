use vstd::prelude::*;
use crate::archive::model_digest::*;
use crate::archive::model_header::*;

verus! {

/// Error type modeling Executive::ExecutiveError.
pub ghost enum ExecutiveError {
    UnableToDecodeExtrinsic,
    InvalidInherentPosition(nat),
    OnlyInherentsAllowed,
    ApplyExtrinsicError,
}

pub type ApplyExtrinsicsResult = Result<(), ExecutiveError>;

pub open spec fn is_only_inherents(mode: ExtrinsicInclusionMode) -> bool {
    match mode {
        ExtrinsicInclusionMode::OnlyInherents => true,
        ExtrinsicInclusionMode::AllExtrinsics => false,
    }
}

/// Recursive spec modeling `Executive::apply_extrinsics` (lib.rs:749-783).
///
/// Parameters:
///   - mode: extrinsic inclusion mode
///   - extrinsics: the full extrinsic list
///   - idx: current iteration index (absolute)
///   - first_non_inherent_idx: tracks the count of leading inherents
///
/// The real code:
/// ```
/// let mut first_non_inherent_idx = 0;
/// for (idx, maybe_uxt) in extrinsics.enumerate() {
///     let is_inherent = ...;
///     if is_inherent {
///         if first_non_inherent_idx != idx { return Err(...) }
///         first_non_inherent_idx += 1;
///     } else {
///         if mode == OnlyInherents { return Err(...) }
///     }
///     if let Err(e) = apply_extrinsic(uxt) { return Err(...) }
/// }
/// Ok(())
/// ```
pub open spec fn apply_extrinsics_spec(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    idx: nat,
    first_non_inherent_idx: nat,
) -> ApplyExtrinsicsResult
    decreases extrinsics.len() - idx,
{
    if idx >= extrinsics.len() {
        Ok(())
    } else {
        let ext = extrinsics[idx as int];

        if ext.is_inherent {
            if first_non_inherent_idx != idx {
                // Inherent after a non-inherent
                Err(ExecutiveError::InvalidInherentPosition(idx))
            } else if !ext.dispatch_succeeds {
                Err(ExecutiveError::ApplyExtrinsicError)
            } else {
                // Continue with incremented first_non_inherent_idx
                apply_extrinsics_spec(mode, extrinsics, idx + 1, first_non_inherent_idx + 1)
            }
        } else {
            if is_only_inherents(mode) {
                Err(ExecutiveError::OnlyInherentsAllowed)
            } else if !ext.dispatch_succeeds {
                Err(ExecutiveError::ApplyExtrinsicError)
            } else {
                // Continue with same first_non_inherent_idx
                apply_extrinsics_spec(mode, extrinsics, idx + 1, first_non_inherent_idx)
            }
        }
    }
}

/// MAIN THEOREM: apply_extrinsics returns Ok(()) for a well-formed block.
///
/// This proves that execute_block does NOT panic at line 711.
pub proof fn theorem_apply_extrinsics_no_panic(
    mode: ExtrinsicInclusionMode,
    extrinsics: Seq<Extrinsic>,
    k: nat,  // inherent boundary: first k are inherents, rest are not
)
    requires
        // Inherent boundary invariant
        k <= extrinsics.len(),
        forall|i: int| 0 <= i < k ==> (#[trigger] extrinsics[i]).is_inherent,
        forall|i: int| k <= i < extrinsics.len() as int
            ==> !(#[trigger] extrinsics[i]).is_inherent,
        // All dispatches succeed
        forall|i: int| 0 <= i < extrinsics.len() as int
            ==> (#[trigger] extrinsics[i]).dispatch_succeeds,
        // OnlyInherents mode implies all extrinsics are inherents
        is_only_inherents(mode) ==> k == extrinsics.len(),
    ensures
        apply_extrinsics_spec(mode, extrinsics, 0, 0) is Ok,
{
    // We prove this by showing it holds for the inherent phase,
    // then the non-inherent phase.
    lemma_inherent_phase(mode, extrinsics, k, 0);
}

/// Lemma: inherent phase (indices 0..k).
/// Invariant: first_non_inherent_idx == pos (they stay in sync for inherents).
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
        is_only_inherents(mode) ==> k == extrinsics.len(),
        pos <= k,
    ensures
        // From position pos with first_non_inherent_idx == pos, the result is Ok
        apply_extrinsics_spec(mode, extrinsics, pos, pos) is Ok,
    decreases extrinsics.len() - pos,
{
    reveal(apply_extrinsics_spec);

    if pos >= extrinsics.len() {
        // pos >= len, so the spec returns Ok(()) immediately
    } else if pos < k {
        // Current extrinsic is an inherent
        let ext = extrinsics[pos as int];
        assert(ext.is_inherent);      // from forall: pos < k → is_inherent
        assert(ext.dispatch_succeeds); // from forall: dispatch_succeeds

        // first_non_inherent_idx == pos == idx → no InvalidInherentPosition error
        // dispatch_succeeds → no ApplyExtrinsicError
        // Recurse: apply_extrinsics_spec(mode, extrinsics, pos+1, pos+1)
        lemma_inherent_phase(mode, extrinsics, k, pos + 1);
    } else {
        // pos == k: transition to non-inherent phase
        assert(pos == k);
        if is_only_inherents(mode) {
            // k == extrinsics.len(), so pos >= len → Ok(())
            assert(k == extrinsics.len());
        } else {
            // Non-inherent phase
            lemma_noninherent_phase(mode, extrinsics, k, pos);
        }
    }
}

/// Lemma: non-inherent phase (indices k..len).
/// first_non_inherent_idx stays at k (frozen).
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
        !is_only_inherents(mode),
        pos >= k,
        pos <= extrinsics.len(),
    ensures
        apply_extrinsics_spec(mode, extrinsics, pos, k) is Ok,
    decreases extrinsics.len() - pos,
{
    reveal(apply_extrinsics_spec);

    if pos >= extrinsics.len() {
        // Past end → Ok(())
    } else {
        let ext = extrinsics[pos as int];
        assert(!ext.is_inherent);      // pos >= k → not inherent
        assert(ext.dispatch_succeeds); // from forall
        assert(!is_only_inherents(mode));

        // The spec branches into the non-inherent path:
        //   !is_only_inherents(mode) → no OnlyInherentsAllowed
        //   dispatch_succeeds → no ApplyExtrinsicError
        //   Recurse: apply_extrinsics_spec(mode, extrinsics, pos+1, k)
        lemma_noninherent_phase(mode, extrinsics, k, pos + 1);
    }
}

} // verus!
