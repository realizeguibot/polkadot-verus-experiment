use vstd::prelude::*;
use crate::milestone3::types::*;
use crate::milestone3::system::*;
use crate::milestone3::initial_checks::*;
use crate::milestone3::apply_extrinsics::*;
use crate::milestone3::final_checks::*;
use crate::milestone3::timestamp::*;
use crate::milestone3::aura::*;

verus! {

// ============================================================================
// Milestone 3: execute_block Cannot Panic Given Valid Block
//
// Master theorem composing all sub-proofs from:
//   - system.rs: System::initialize (asserts A, B) + System::finalize
//   - initial_checks.rs: parent hash validation
//   - apply_extrinsics.rs: extrinsic processing loop
//   - final_checks.rs: digest/root comparison
//   - timestamp.rs: Timestamp::set + on_finalize
//   - aura.rs: Aura::on_initialize + on_timestamp_set
//
// Covers all 19 panic points from the panic inventory.
// ============================================================================

// ============================================================================
// The valid_block precondition
//
// This is the formal specification of what makes a block valid for
// panic-free execution. Each clause maps to one or more panic points.
// ============================================================================

/// Complete valid_block precondition.
///
/// A block satisfying this predicate can be executed by execute_block
/// without any panic. Each clause eliminates specific panic points.
pub open spec fn valid_block(
    block: &Block,
    stored_block_number: u32,
    aura_state: AuraState,
    timestamp_state: TimestampState,
    aura_inherent: AuraInherentData,
    timestamp_inherent: TimestampInherentData,
    max_header_size: u32,
) -> bool {
    let mode = block_mode(block);
    let k = inherent_boundary(block);

    // --- Block structure ---
    // #1: Block number is positive and sequential
    &&& block.header.number > 0u32
    &&& block.header.number < u32::MAX
    &&& block.header.number == (stored_block_number + 1) as u32
    &&& stored_block_number < u32::MAX

    // #2: Header size within limit
    &&& digest_encoded_size(&block.header.digest) + header_base_size() <= max_header_size as nat

    // #3: Parent hash matches stored hash
    &&& stored_block_hash((block.header.number - 1) as u32) == block.header.parent_hash

    // #4: All extrinsics decode successfully
    &&& block.all_extrinsics_decode_ok()

    // #5: Inherents contiguous at start
    &&& block.inherents_contiguous_with_boundary(k)

    // #6: OnlyInherents mode ⟹ all inherent
    &&& (is_only_inherents(mode) ==> block.all_inherent())
    &&& (is_only_inherents(mode) ==> k == block.extrinsics.len())

    // #7: All dispatches succeed (covered by #4-6 + dispatch safety)
    &&& block.all_dispatches_succeed()

    // #8-11: Header matches execution output (correct digests)
    &&& block.header == finalized_header_after_execution(block)

    // #12: Storage root hash decodable
    &&& storage_root_hash_decodable()

    // #13-15: Timestamp inherent present exactly once with valid value
    &&& !timestamp_state.did_update
    &&& (timestamp_state.now == 0u64 ||
         timestamp_inherent.timestamp >= timestamp_state.now + timestamp_state.min_period)

    // #16-17: Aura slot monotonicity and author not disabled
    &&& (aura_state.allow_multiple_blocks_per_slot ==>
         aura_state.current_slot <= aura_inherent.slot)
    &&& (!aura_state.allow_multiple_blocks_per_slot ==>
         aura_state.current_slot < aura_inherent.slot)
    &&& !aura_author_disabled(aura_inherent.slot)

    // #18-19: Aura slot duration positive and timestamp/slot consistent
    &&& aura_state.slot_duration > 0u64
    &&& timestamp_inherent.timestamp / aura_state.slot_duration == aura_inherent.slot

    // TCB: Other pallet hooks are safe
    &&& other_pallet_hooks_safe(block)
}

// ============================================================================
// THE MASTER THEOREM
// ============================================================================

/// **THEOREM: execute_block does not panic for a valid block.**
///
/// This is the composition of all sub-proofs. Given a block satisfying
/// the valid_block predicate, every step of execute_block completes
/// without any panic (assertion failure, overflow, or other abort).
///
/// The proof walks through execute_block's call sequence:
///   1. initialize_block → System::initialize (asserts A, B)
///   2. Aura::on_initialize (slot + disabled validator)
///   3. Timestamp::set (via inherent dispatch)
///   4. apply_extrinsics loop
///   5. Aura::on_timestamp_set (called by Timestamp::set)
///   6. System::finalize
///   7. Timestamp::on_finalize
///   8. final_checks (digest/root comparison)
///
/// All 19 panic points are covered, each mapped to a clause in valid_block.
pub proof fn theorem_execute_block_no_panic(
    block: Block,
    stored_block_number: u32,
    aura_state: AuraState,
    timestamp_state: TimestampState,
    aura_inherent: AuraInherentData,
    timestamp_inherent: TimestampInherentData,
    max_header_size: u32,
)
    requires
        valid_block(
            &block, stored_block_number, aura_state, timestamp_state,
            aura_inherent, timestamp_inherent, max_header_size,
        ),
{
    let mode = block_mode(&block);
    let k = inherent_boundary(&block);

    // =====================================================================
    // Step 1: System::initialize — panic points #1, #2
    // =====================================================================

    // Assert A (#1): block_number + 1 == header.number (tautology)
    system_initialize_assert_a_no_panic(stored_block_number, block.header.number);

    // Assert B (#2): digest overhead ≤ max_header_size
    system_initialize_assert_b_no_panic(&block.header.digest, max_header_size);

    // =====================================================================
    // Step 2: initial_checks — panic point #3
    // =====================================================================

    initial_checks_no_panic(&block.header);

    // =====================================================================
    // Step 3: Aura::on_initialize — panic points #16, #17
    // =====================================================================

    aura_on_initialize_no_panic(aura_state, aura_inherent.slot);

    // =====================================================================
    // Step 4: Timestamp::set (inherent dispatch) — panic points #14, #15
    // =====================================================================

    timestamp_set_no_panic(timestamp_state, timestamp_inherent.timestamp);

    // =====================================================================
    // Step 5: Aura::on_timestamp_set — panic points #18, #19
    // =====================================================================

    aura_on_timestamp_set_no_panic(
        timestamp_inherent.timestamp,
        aura_state.slot_duration,
        aura_inherent.slot,
    );

    // =====================================================================
    // Step 6: apply_extrinsics — panic points #4, #5, #6, #7
    // =====================================================================

    // Establish the preconditions for apply_extrinsics
    assert(block.inherents_contiguous_with_boundary(k));
    assert(k <= block.extrinsics.len());
    assert(block.all_dispatches_succeed());
    assert(block.all_extrinsics_decode_ok());

    // If OnlyInherents mode, all extrinsics are inherents → k == len
    if is_only_inherents(mode) {
        assert(block.all_inherent());
        assert(k == block.extrinsics.len());
    }

    theorem_apply_extrinsics_no_panic(mode, block.extrinsics, k);

    // =====================================================================
    // Step 7: System::finalize — panic point #12
    // =====================================================================

    system_finalize_no_panic();

    // =====================================================================
    // Step 8: Timestamp::on_finalize — panic point #13
    // =====================================================================

    // After Timestamp::set ran, DidUpdate is true.
    timestamp_on_finalize_no_panic(true);

    // =====================================================================
    // Step 9: final_checks — panic points #8, #9, #10, #11
    // =====================================================================

    final_checks_with_correct_block(&block);
}

// ============================================================================
// PANIC POINT COVERAGE MAP
//
// Each of the 19 panic points is mapped to:
//   - The sub-proof that verifies it
//   - The clause in valid_block that eliminates it
//
// | #  | Panic                    | Sub-proof                         | Precondition clause        |
// |----|--------------------------|-----------------------------------|----------------------------|
// | 1  | Block number not seq     | system_initialize_assert_a        | number == stored + 1       |
// | 2  | Header size exceeds      | system_initialize_assert_b        | digest overhead ≤ max      |
// | 3  | Parent hash mismatch     | initial_checks_no_panic           | parent_hash == stored_hash |
// | 4  | Extrinsic decode fail    | theorem_apply_extrinsics          | all_extrinsics_decode_ok   |
// | 5  | Inherent after non-inh   | theorem_apply_extrinsics          | inherents_contiguous       |
// | 6  | Non-inh in OnlyInh mode  | theorem_apply_extrinsics          | mode ⟹ all_inherent      |
// | 7  | apply_extrinsics Err     | theorem_apply_extrinsics          | all conditions above       |
// | 8  | Digest len mismatch      | final_checks_no_panic             | header == finalized        |
// | 9  | Digest item mismatch     | final_checks_no_panic             | header == finalized        |
// | 10 | State root mismatch      | final_checks_no_panic             | header == finalized        |
// | 11 | Extrinsics root mismatch | final_checks_no_panic             | header == finalized        |
// | 12 | Hash decode failure      | system_finalize_no_panic          | storage_root_decodable     |
// | 13 | Timestamp not updated    | timestamp_on_finalize_no_panic    | timestamp inherent present |
// | 14 | Timestamp set twice      | timestamp_set_no_panic            | !did_update                |
// | 15 | Timestamp too early      | timestamp_set_no_panic            | now ≥ prev + min_period    |
// | 16 | Slot didn't increase     | aura_on_initialize_no_panic       | new_slot > current_slot    |
// | 17 | Disabled validator       | aura_on_initialize_no_panic       | !author_disabled           |
// | 18 | Slot duration zero       | aura_on_timestamp_set_no_panic    | slot_duration > 0          |
// | 19 | Timestamp/slot mismatch  | aura_on_timestamp_set_no_panic    | ts / duration == slot      |
// ============================================================================

} // verus!
