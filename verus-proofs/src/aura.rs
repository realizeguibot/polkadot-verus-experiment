use vstd::prelude::*;

verus! {

// ============================================================================
// Ported from: substrate/frame/aura/src/lib.rs
//
// Two functions with panics:
//   1. Aura::on_initialize (lines 128-157) — slot monotonicity + disabled validator
//   2. Aura::on_timestamp_set (lines 410-425) — slot duration + timestamp/slot consistency
//
// Both are exec fns with real u64 arithmetic.
// ============================================================================

// ============================================================================
// Aura::on_initialize — ported from aura/src/lib.rs:128-157
//
// fn on_initialize(_: BlockNumberFor<T>) -> Weight {
//     if let Some(new_slot) = Self::current_slot_from_digests() {
//         let current_slot = CurrentSlot::<T>::get();
//         if T::AllowMultipleBlocksPerSlot::get() {
//             assert!(current_slot <= new_slot, "Slot must not decrease");
//         } else {
//             assert!(current_slot < new_slot, "Slot must increase");
//         }
//         CurrentSlot::<T>::put(new_slot);
//         if let Some(n_authorities) = <Authorities<T>>::decode_len() {
//             let authority_index = *new_slot % n_authorities as u64;
//             if T::DisabledValidators::is_disabled(authority_index as u32) {
//                 panic!("Validator with index {:?} is disabled...", authority_index);
//             }
//         }
//         ...
//     }
// }
//
// Panic points:
//   Line 133: assert!(current_slot <= new_slot) — slot went backwards
//   Line 135: assert!(current_slot < new_slot) — slot didn't advance
//   Line 143: panic!("Validator disabled") — block author is disabled
//
// Note: the `*new_slot % n_authorities as u64` uses u64 modulus, which
// never panics (n_authorities > 0 for the Some branch of decode_len).
// The `as u32` cast on authority_index could theoretically truncate, but
// that's just an index passed to is_disabled, not a panic source itself.
// ============================================================================

/// Faithful port of Aura::on_initialize.
///
/// Parameters replace storage/config reads:
///   slot_found          ← Self::current_slot_from_digests().is_some()
///   new_slot            ← the slot value from the digest
///   current_slot        ← CurrentSlot::<T>::get()
///   allow_multiple      ← T::AllowMultipleBlocksPerSlot::get()
///   has_authorities     ← <Authorities<T>>::decode_len().is_some()
///   n_authorities       ← the authority count (only used if has_authorities)
///   author_disabled     ← T::DisabledValidators::is_disabled(authority_index)
pub fn aura_on_initialize(
    slot_found: bool,
    new_slot: u64,
    current_slot: u64,
    allow_multiple: bool,
    has_authorities: bool,
    n_authorities: u64,
    author_disabled: bool,
)
    requires
        // If a slot was found in the digest:
        slot_found ==> (
            // Slot monotonicity
            (allow_multiple ==> current_slot <= new_slot)
            && (!allow_multiple ==> current_slot < new_slot)
            // Author not disabled
            && (has_authorities ==> !author_disabled)
            // n_authorities > 0 when authorities exist (for modulus safety)
            && (has_authorities ==> n_authorities > 0u64)
        ),
{
    // --- Line 129 ---
    // if let Some(new_slot) = Self::current_slot_from_digests()
    if slot_found {
        // --- Lines 132-136 ---
        if allow_multiple {
            // assert!(current_slot <= new_slot, "Slot must not decrease");
            assert(current_slot <= new_slot);
        } else {
            // assert!(current_slot < new_slot, "Slot must increase");
            assert(current_slot < new_slot);
        }

        // --- Lines 140-148 ---
        // if let Some(n_authorities) = <Authorities<T>>::decode_len()
        if has_authorities {
            // let authority_index = *new_slot % n_authorities as u64;
            let authority_index: u64 = new_slot % n_authorities;
            //                         ^^^^^^^^^^^^^^^^^^^^^^^^^^ Verus checks: n_authorities != 0
            //                         (guaranteed by requires: n_authorities > 0)

            // if T::DisabledValidators::is_disabled(authority_index as u32) { panic!(...) }
            if author_disabled {
                // This is the panic!() at line 143. We prove it's unreachable.
                assert(false); // unreachable: requires says !author_disabled when has_authorities
            }
        }
    }
    // else: no slot found, no panics possible
}

// ============================================================================
// Aura::on_timestamp_set — ported from aura/src/lib.rs:410-424
//
// fn on_timestamp_set(moment: T::Moment) {
//     let slot_duration = Self::slot_duration();
//     assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");
//     let timestamp_slot = moment / slot_duration;
//     let timestamp_slot = Slot::from(timestamp_slot.saturated_into::<u64>());
//     assert_eq!(CurrentSlot::<T>::get(), timestamp_slot, "Timestamp slot must match...");
// }
//
// Panic points:
//   Line 412: assert!(!slot_duration.is_zero()) — zero slot duration
//   Line 417: assert_eq!(current_slot, timestamp_slot) — timestamp/slot inconsistency
//
// Note: `moment / slot_duration` is u64 integer division. Safe when divisor != 0.
// `saturated_into::<u64>()` on a u64 is identity (no-op).
// ============================================================================

/// Faithful port of Aura::on_timestamp_set.
///
/// Parameters:
///   moment        ← the timestamp moment
///   slot_duration ← Self::slot_duration()
///   current_slot  ← CurrentSlot::<T>::get() (updated by on_initialize)
pub fn aura_on_timestamp_set(
    moment: u64,
    slot_duration: u64,
    current_slot: u64,
)
    requires
        // Slot duration is positive (configured at genesis, never zero)
        slot_duration > 0u64,
        // The timestamp is consistent with the slot
        moment / slot_duration == current_slot,
{
    // --- Line 412 ---
    // assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");
    assert(slot_duration != 0u64);
    //      ^^^^^^^^^^^^^^^^^^ Verus checks: equivalent to slot_duration > 0

    // --- Lines 414-415 ---
    // let timestamp_slot = moment / slot_duration;
    let timestamp_slot: u64 = moment / slot_duration;
    //                        ^^^^^^^^^^^^^^^^^^^^^^^ Verus checks: slot_duration != 0 (no div-by-zero)

    // --- Lines 417-423 ---
    // assert_eq!(CurrentSlot::<T>::get(), timestamp_slot, "...");
    assert(current_slot == timestamp_slot);
}

} // verus!
