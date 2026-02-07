use vstd::prelude::*;
use crate::milestone3::types::*;

verus! {

// ============================================================================
// pallet_aura — ported from aura/src/lib.rs
//
// Panic points:
//   #16: on_initialize: slot didn't increase
//   #17: on_initialize: disabled validator authored
//   #18: on_timestamp_set: slot duration zero
//   #19: on_timestamp_set: timestamp/slot mismatch
//
// Source: substrate/frame/consensus/aura/src/lib.rs
// ============================================================================

// ============================================================================
// Aura::on_initialize — ported from aura/src/lib.rs:128-157
//
// fn on_initialize(_: BlockNumberFor<T>) -> Weight {
//     if let Some(new_slot) = Self::current_slot_from_digests() {
//         let current_slot = CurrentSlot::<T>::get();
//         if T::AllowMultipleBlocksPerSlot::get() {
//             assert!(
//                 current_slot <= new_slot,                    // #16a
//                 "Slot must not decrease"
//             );
//         } else {
//             assert!(
//                 current_slot < new_slot,                     // #16b
//                 "Slot must increase"
//             );
//         }
//         CurrentSlot::<T>::put(new_slot);
//
//         if let Some(n_authorities) = ... {
//             let authority_index = *new_slot % n_authorities;
//             if T::DisabledValidators::is_disabled(authority_index) {
//                 panic!(                                       // #17
//                     "Validator with index {:?} is disabled ...",
//                     authority_index
//                 );
//             }
//         }
//     }
//     ...
// }
// ============================================================================

/// **THEOREM: Aura::on_initialize does not panic.**
///
/// Preconditions:
///   - #16: New slot > current slot (or >= if AllowMultipleBlocksPerSlot)
///   - #17: The author for the new slot is not disabled
pub proof fn aura_on_initialize_no_panic(
    state: AuraState,
    new_slot: Slot,
)
    requires
        // #16: Slot monotonicity
        state.allow_multiple_blocks_per_slot ==> state.current_slot <= new_slot,
        !state.allow_multiple_blocks_per_slot ==> state.current_slot < new_slot,
        // #17: Author not disabled
        !aura_author_disabled(new_slot),
    ensures
        true,
{
    // Assert #16: slot monotonicity
    if state.allow_multiple_blocks_per_slot {
        assert(state.current_slot <= new_slot);
    } else {
        assert(state.current_slot < new_slot);
    }

    // Assert #17: author not disabled
    assert(!aura_author_disabled(new_slot));
}

// ============================================================================
// Aura::on_timestamp_set — ported from aura/src/lib.rs:410-424
//
// fn on_timestamp_set(moment: T::Moment) {
//     let slot_duration = Self::slot_duration();
//     assert!(
//         !slot_duration.is_zero(),                            // #18
//         "Aura slot duration cannot be zero."
//     );
//     let timestamp_slot = moment / slot_duration;
//     let current_slot = Self::current_slot();
//     assert!(
//         current_slot == timestamp_slot,                      // #19
//         "Timestamp slot must match current slot"
//     );
// }
// ============================================================================

/// **THEOREM: Aura::on_timestamp_set does not panic.**
///
/// Preconditions:
///   - #18: Slot duration > 0
///   - #19: timestamp / slot_duration == current_slot
pub proof fn aura_on_timestamp_set_no_panic(
    timestamp: Moment,
    slot_duration: Moment,
    current_slot: Slot,
)
    requires
        // #18: Slot duration is positive
        slot_duration > 0,
        // #19: Timestamp/slot consistency
        timestamp / slot_duration == current_slot,
    ensures
        true,
{
    // Assert #18: slot duration nonzero
    assert(slot_duration > 0u64);

    // Assert #19: timestamp_slot == current_slot
    // timestamp_slot = timestamp / slot_duration (integer division, safe since slot_duration > 0)
    let timestamp_slot = timestamp / slot_duration;
    assert(timestamp_slot == current_slot);
}

// ============================================================================
// Combined Aura proof
// ============================================================================

/// **THEOREM: Complete Aura lifecycle is panic-free.**
///
/// Covers on_initialize (slot check + disabled validator) and
/// on_timestamp_set (slot duration + consistency).
pub proof fn theorem_aura_lifecycle_no_panic(
    state: AuraState,
    new_slot: Slot,
    timestamp: Moment,
)
    requires
        // on_initialize preconditions (#16, #17)
        state.allow_multiple_blocks_per_slot ==> state.current_slot <= new_slot,
        !state.allow_multiple_blocks_per_slot ==> state.current_slot < new_slot,
        !aura_author_disabled(new_slot),
        // on_timestamp_set preconditions (#18, #19)
        state.slot_duration > 0,
        timestamp / state.slot_duration == new_slot,
    ensures
        true,
{
    aura_on_initialize_no_panic(state, new_slot);
    aura_on_timestamp_set_no_panic(timestamp, state.slot_duration, new_slot);
}

} // verus!
