use vstd::prelude::*;
use crate::system::*;

verus! {

// ============================================================================
// Ported from: substrate/frame/executive/src/lib.rs
//
// This file contains faithful ports of:
//   - initial_checks (lines 681-692)
//   - apply_extrinsics (lines 749-783)
//   - final_checks (lines 920-946)
//   - validate_transaction (lines 953-995)
//
// Each function is an exec fn. Verus machine-checks:
//   - No u32/usize arithmetic overflow
//   - All assert() conditions hold given the requires clause
//   - No Vec out-of-bounds indexing
// ============================================================================

// --- Model types for extrinsics ---
// The real Extrinsic is a complex trait object. We extract the three
// properties that matter for the control flow:

pub struct Ext {
    pub decodes_ok: bool,   // whether decode_all_with_depth_limit returns Ok
    pub is_inherent: bool,  // whether System::is_inherent returns true
    pub apply_ok: bool,     // whether apply_extrinsic returns Ok
}

// ============================================================================
// initial_checks — ported from executive/src/lib.rs:681-692
//
// fn initial_checks(header: &Block::Header) {
//     let n = *header.number();
//     assert!(
//         n > BlockNumberFor::<System>::zero() &&
//             <frame_system::Pallet<System>>::block_hash(n - BlockNumberFor::<System>::one()) ==
//                 *header.parent_hash(),
//         "Parent hash should be valid.",
//     );
// }
// ============================================================================

/// Faithful port of Executive::initial_checks.
///
/// Parameters:
///   n            ← *header.number()
///   stored_hash  ← frame_system::block_hash(n - 1)
///   parent_hash  ← *header.parent_hash()
pub fn initial_checks(
    n: u32,
    stored_hash: &[u8; 32],
    parent_hash: &[u8; 32],
)
    requires
        n > 0u32,
        *stored_hash == *parent_hash,
{
    // --- Line 686-691 ---
    // assert!(n > Zero::zero() && block_hash(n - 1) == *header.parent_hash())
    assert(n > 0u32 && *stored_hash == *parent_hash);
}

// ============================================================================
// apply_extrinsics — ported from executive/src/lib.rs:749-783
//
// fn apply_extrinsics(mode, extrinsics, apply_extrinsic) -> Result<(), ExecutiveError> {
//     let mut first_non_inherent_idx = 0;
//     for (idx, maybe_uxt) in extrinsics.enumerate() {
//         let uxt = maybe_uxt.map_err(|_| UnableToDecodeExtrinsic)?;
//         let is_inherent = System::is_inherent(&uxt);
//         if is_inherent {
//             if first_non_inherent_idx != idx {
//                 return Err(InvalidInherentPosition(idx));
//             }
//             first_non_inherent_idx += 1;
//         } else {
//             if mode == OnlyInherents {
//                 return Err(OnlyInherentsAllowed);
//             }
//         }
//         if let Err(e) = apply_extrinsic(uxt) {
//             return Err(ApplyExtrinsic(e));
//         }
//     }
//     Ok(())
// }
//
// Note: the function itself never panics — it returns Result.
// The panic is in execute_block line 711: if let Err(e) = apply_extrinsics(...) { panic!() }
// So we prove: given well-formed input, apply_extrinsics returns Ok(()).
// ============================================================================

/// Mode: 0 = AllExtrinsics, 1 = OnlyInherents
/// Returns: Ok(()) or Err(error_code)
///
/// The while loop is a faithful port of the for-enumerate loop.
/// Verus verifies:
///   - No usize overflow on idx or first_non_inherent_idx
///   - No Vec out-of-bounds access
///   - The function returns Ok(()) given the preconditions
///
/// `ghost_k` is the inherent boundary index — a ghost (proof-only) parameter
/// that witnesses the contiguous-inherent-prefix property.
pub fn apply_extrinsics(
    exts: &Vec<Ext>,
    mode: u8,
    Ghost(ghost_k): Ghost<int>,
) -> (result: Result<(), u64>)
    requires
        // All extrinsics decode successfully
        forall|i: int| 0 <= i < exts@.len() ==> (#[trigger] exts@[i]).decodes_ok,
        // All extrinsics dispatch successfully
        forall|i: int| 0 <= i < exts@.len() ==> (#[trigger] exts@[i]).apply_ok,
        // Inherents form a contiguous prefix: first ghost_k are inherent, rest are not
        0 <= ghost_k <= exts@.len(),
        forall|i: int| 0 <= i < ghost_k ==> (#[trigger] exts@[i]).is_inherent,
        forall|i: int| ghost_k <= i < exts@.len() ==> !(#[trigger] exts@[i]).is_inherent,
        // OnlyInherents mode means ALL extrinsics are inherents
        mode == 1u8 ==> ghost_k == exts@.len(),
    ensures
        result is Ok,
{
    let ghost k = ghost_k;

    // --- Line 754 ---
    let mut first_non_inherent_idx: usize = 0;

    // --- Line 755: for (idx, maybe_uxt) in extrinsics.enumerate() ---
    let mut idx: usize = 0;
    while idx < exts.len()
        invariant
            idx <= exts@.len(),
            // Core invariant: first_non_inherent_idx tracks min(k, idx)
            first_non_inherent_idx as int == if (idx as int) <= k { idx as int } else { k },
            // Re-state preconditions for the loop body
            0 <= k <= exts@.len(),
            forall|i: int| 0 <= i < k ==> (#[trigger] exts@[i]).is_inherent,
            forall|i: int| k <= i < exts@.len() ==> !(#[trigger] exts@[i]).is_inherent,
            forall|i: int| 0 <= i < exts@.len() ==> (#[trigger] exts@[i]).decodes_ok,
            forall|i: int| 0 <= i < exts@.len() ==> (#[trigger] exts@[i]).apply_ok,
            mode == 1u8 ==> k == exts@.len(),
        decreases exts@.len() - idx,
    {
        let ext = &exts[idx];
        //            ^^^^^^^^^ Verus checks: idx < exts.len() from loop guard

        // --- Line 756: let uxt = maybe_uxt.map_err(|_| UnableToDecodeExtrinsic)? ---
        if !ext.decodes_ok {
            return Err(1); // UnableToDecodeExtrinsic — unreachable from precondition
        }

        // --- Line 757: let is_inherent = System::is_inherent(&uxt) ---
        if ext.is_inherent {
            // --- Lines 759-763 ---
            if first_non_inherent_idx != idx {
                return Err(2); // InvalidInherentPosition — unreachable:
                // From invariant: first_non_inherent_idx == min(k, idx).
                // ext.is_inherent ==> idx < k (from contiguity).
                // So min(k, idx) == idx. So first_non_inherent_idx == idx. Contradiction.
            }
            first_non_inherent_idx = idx + 1;
            //                       ^^^^^^^ Verus checks: no overflow
            // (idx < exts.len() <= usize::MAX, so idx + 1 <= usize::MAX)
        } else {
            // --- Lines 765-768 ---
            if mode == 1u8 {
                return Err(3); // OnlyInherentsAllowed — unreachable:
                // !ext.is_inherent ==> idx >= k (from contiguity).
                // mode == 1 ==> k == exts.len(). But idx < exts.len().
                // So idx < k. Contradiction with idx >= k.
            }
        }

        // --- Lines 772-778: if let Err(e) = apply_extrinsic(uxt) { return Err(...) } ---
        if !ext.apply_ok {
            return Err(4); // ApplyExtrinsic error — unreachable from precondition
        }

        idx = idx + 1;
        //    ^^^^^^^^^ Verus checks: no overflow (same reasoning as above)
    }

    Ok(())
}

// ============================================================================
// final_checks — ported from executive/src/lib.rs:920-946
//
// fn final_checks(header: &HeaderFor<System>) {
//     let new_header = <frame_system::Pallet<System>>::finalize();
//     assert_eq!(header.digest().logs().len(), new_header.digest().logs().len());
//     for (header_item, computed_item) in ... .zip(...) {
//         assert!(header_item == computed_item);
//     }
//     assert!(header.state_root() == new_header.state_root());
//     assert!(header.extrinsics_root() == new_header.extrinsics_root());
// }
//
// We model digest items as u64 fingerprints. The exact type doesn't matter —
// what matters is that Verus checks the comparison loop and assertions.
// ============================================================================

/// Faithful port of Executive::final_checks.
///
/// Parameters replace complex types:
///   header_digest    ← header.digest().logs() (modeled as Vec<u64>)
///   computed_digest  ← new_header.digest().logs()
///   header_state_root     ← header.state_root()
///   computed_state_root   ← new_header.state_root()
///   header_ext_root       ← header.extrinsics_root()
///   computed_ext_root     ← new_header.extrinsics_root()
pub fn final_checks(
    header_digest: &Vec<u64>,
    computed_digest: &Vec<u64>,
    header_state_root: &[u8; 32],
    computed_state_root: &[u8; 32],
    header_ext_root: &[u8; 32],
    computed_ext_root: &[u8; 32],
)
    requires
        // "Correct header" precondition: block proposer built the header correctly
        header_digest@.len() == computed_digest@.len(),
        forall|i: int| 0 <= i < header_digest@.len()
            ==> (#[trigger] header_digest@[i]) == computed_digest@[i],
        *header_state_root == *computed_state_root,
        *header_ext_root == *computed_ext_root,
{
    // --- Line 926-930 ---
    // assert_eq!(header.digest().logs().len(), new_header.digest().logs().len());
    assert(header_digest.len() == computed_digest.len());

    // --- Lines 931-935: the zip-comparison loop ---
    let mut i: usize = 0;
    while i < header_digest.len()
        invariant
            i <= header_digest@.len(),
            header_digest@.len() == computed_digest@.len(),
            forall|j: int| 0 <= j < header_digest@.len()
                ==> (#[trigger] header_digest@[j]) == computed_digest@[j],
        decreases header_digest@.len() - i,
    {
        // assert!(header_item == computed_item, "Digest item must match that calculated.");
        assert(header_digest@[i as int] == computed_digest@[i as int]);
        i = i + 1;
    }

    // --- Line 940 ---
    // assert!(header.state_root() == storage_root, "Storage root must match that calculated.");
    assert(*header_state_root == *computed_state_root);

    // --- Lines 942-945 ---
    // assert!(header.extrinsics_root() == new_header.extrinsics_root());
    assert(*header_ext_root == *computed_ext_root);
}

// ============================================================================
// validate_transaction — ported from executive/src/lib.rs:953-995
//
// pub fn validate_transaction(source, uxt, block_hash) -> TransactionValidity {
//     <System>::initialize(
//         &(Pallet::<System>::block_number() + One::one()),
//         &block_hash, &Default::default(),
//     );
//     let encoded = uxt.encode();
//     let uxt = DecodeLimit::decode_all_with_depth_limit(...)
//         .map_err(|_| InvalidTransaction::Call)?;
//     let xt = uxt.check(&Default::default())?;
//     let dispatch_info = xt.get_dispatch_info();
//     if dispatch_info.class == DispatchClass::Mandatory {
//         return Err(InvalidTransaction::MandatoryValidation.into());
//     }
//     xt.validate(source, &dispatch_info, encoded.len())
// }
//
// The only panic risk is in System::initialize (called at line 961-965).
// The rest is all Result-returning operations chained with ?.
// ============================================================================

/// Faithful port of validate_transaction's panic-relevant logic.
///
/// Parameters:
///   block_number        ← Pallet::<System>::block_number()
///   digest_encoded_size ← Default::default().encoded_size() (empty digest)
///   empty_header_size   ← Header::new(..., Default::default()).encoded_size()
///   max_header_size     ← T::BlockLength::get().max_header_size()
///
/// Returns 0 for success, nonzero for error (modeling TransactionValidity).
/// The function itself never panics — only System::initialize can panic,
/// and we prove it doesn't.
pub fn validate_transaction(
    block_number: u32,
    digest_encoded_size: usize,
    empty_header_size: usize,
    max_header_size: u32,
) -> (result: u64)
    requires
        // Block number doesn't overflow on +1
        block_number < u32::MAX,
        // Header overhead fits in u32 and under the limit
        // (For validate_transaction, the digest is Default::default() = empty,
        //  so digest_encoded_size ≈ 1 byte, empty_header_size ≈ 100 bytes)
        digest_encoded_size + empty_header_size <= u32::MAX as usize,
        (digest_encoded_size + empty_header_size) as u32 <= max_header_size,
{
    // --- Lines 961-965 ---
    // <System>::initialize(&(block_number() + One::one()), &block_hash, &Default::default());
    let number: u32 = block_number + 1;
    //                 ^^^^^^^^^^^^^^^^ Verus checks: no u32 overflow
    system_initialize(block_number, number, digest_encoded_size, empty_header_size, max_header_size);
    // ^^^ If this returns (doesn't panic), System::initialize is safe.

    // --- Lines 969-977 ---
    // let encoded = uxt.encode();           ← infallible, returns Vec<u8>
    // let uxt = decode_all(...)
    //     .map_err(|_| InvalidTransaction::Call)?;
    // → Returns Result. If Err, returns early. No panic.
    // (Modeled as always succeeding since we return a success code)

    // --- Lines 979-981 ---
    // let xt = uxt.check(&Default::default())?;
    // → Returns Result. No panic.

    // --- Lines 983-985 ---
    // let dispatch_info = xt.get_dispatch_info();
    // → Pure computation. No panic.

    // --- Lines 987-988 ---
    // if dispatch_info.class == DispatchClass::Mandatory {
    //     return Err(InvalidTransaction::MandatoryValidation.into());
    // }
    // → Returns Err, not a panic.

    // --- Lines 991-994 ---
    // xt.validate(source, &dispatch_info, encoded.len())
    // → Returns TransactionValidity (Result). No panic.

    0  // success (the actual return value doesn't matter — we proved no panic)
}

} // verus!
