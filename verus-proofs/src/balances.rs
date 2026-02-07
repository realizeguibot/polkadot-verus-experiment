use vstd::prelude::*;

verus! {

// ============================================================================
// Ported from: substrate/frame/balances/src/lib.rs
//
// This file contains faithful ports of the two panic-relevant code paths
// in pallet_balances:
//
//   1. The "dust check" defensive assert in try_mutate_account (lines 1130-1143)
//   2. The guarded subtraction in force_set_balance (lines 809-812)
//
// Both are exec fns with real u128 arithmetic. Verus machine-checks:
//   - No underflow on the subtractions in force_set_balance
//   - The assert! condition in the dust check always holds
// ============================================================================

// ============================================================================
// try_mutate_account dust check — ported from balances/src/lib.rs:1130-1143
//
// let ed = Self::ed();
// let maybe_dust = if account.free < ed && account.reserved.is_zero() {
//     if account.free.is_zero() {
//         None
//     } else {
//         Some(account.free)
//     }
// } else {
//     assert!(
//         account.free.is_zero() || account.free >= ed || !account.reserved.is_zero()
//     );
//     *maybe_account = Some(account);
//     None
// };
//
// The assert! at line 1138 is a defensive check. It fires if:
//   - We're in the else branch (meaning: !(free < ed && reserved == 0))
//   - BUT the disjunction doesn't hold
//
// We prove: the assert! NEVER fires, because the else-branch condition
// logically implies the assert condition. This is a tautology proof
// on REAL u128 values, not ghost types.
// ============================================================================

/// Faithful port of the dust-check logic in try_mutate_account.
///
/// Parameters map directly to account fields:
///   free     ← account.free
///   reserved ← account.reserved
///   ed       ← Self::ed() (existential deposit)
///
/// Verus verifies: the assert() on line 1138 can never fail,
/// because being in the else branch guarantees the condition.
pub fn dust_check(free: u128, reserved: u128, ed: u128)
    requires
        // Existential deposit is positive.
        // Enforced by pallet_balances::integrity_test, always true for Asset Hub.
        ed > 0u128,
{
    // --- Line 1131 ---
    if free < ed && reserved == 0 {
        // Dust removal path.
        // --- Lines 1132-1136 ---
        if free == 0 {
            // None — already zero, no dust
        } else {
            // Some(free) — will emit DustLost event
        }
    } else {
        // --- Line 1138-1140 ---
        // assert!(account.free.is_zero() || account.free >= ed || !account.reserved.is_zero());
        //
        // WHY THIS HOLDS:
        //   We're in the else branch, so: !(free < ed && reserved == 0)
        //   By De Morgan: (free >= ed) || (reserved != 0)
        //   This implies: (free == 0) || (free >= ed) || (reserved != 0)
        //   because (free >= ed) is the middle disjunct.
        //
        // Verus checks this automatically from the if/else branching.
        assert(free == 0 || free >= ed || reserved != 0);
    }
}

// ============================================================================
// force_set_balance imbalance — ported from balances/src/lib.rs:809-812
//
// if new_free > old_free {
//     mem::drop(PositiveImbalance::<T, I>::new(new_free - old_free));
// } else if new_free < old_free {
//     mem::drop(NegativeImbalance::<T, I>::new(old_free - new_free));
// }
//
// Each subtraction is guarded by a strict inequality comparison.
// Verus checks: no u128 underflow.
// ============================================================================

/// Faithful port of force_set_balance's imbalance calculation.
///
/// Parameters:
///   new_free ← the new balance after wipeout adjustment (line 798)
///   old_free ← the previous account.free (line 802)
///
/// Verus verifies: neither subtraction underflows,
/// because each is guarded by a comparison.
pub fn force_set_balance_imbalance(new_free: u128, old_free: u128)
{
    // --- Lines 809-812 ---
    if new_free > old_free {
        let _positive_imbalance = new_free - old_free;
        //                        ^^^^^^^^^^^^^^^^^^^^ Verus checks: new_free > old_free ⟹ no underflow
    } else if new_free < old_free {
        let _negative_imbalance = old_free - new_free;
        //                        ^^^^^^^^^^^^^^^^^^^^ Verus checks: old_free > new_free ⟹ no underflow
    }
    // else: new_free == old_free, no imbalance, no subtraction
}

// ============================================================================
// force_set_balance wipeout logic — ported from balances/src/lib.rs:797-798
//
// let wipeout = new_free < existential_deposit;
// let new_free = if wipeout { Zero::zero() } else { new_free };
//
// This is pure comparison + conditional, no panic risk.
// But we port it to show the complete force_set_balance control flow.
// ============================================================================

/// Port of force_set_balance's wipeout + imbalance logic combined.
///
/// Parameters:
///   input_new_free ← the new_free parameter to the dispatchable
///   old_free       ← the account's current free balance
///   ed             ← Self::ed()
pub fn force_set_balance_full(input_new_free: u128, old_free: u128, ed: u128)
    requires
        ed > 0u128,
{
    // --- Lines 797-798 ---
    // let wipeout = new_free < existential_deposit;
    // let new_free = if wipeout { Zero::zero() } else { new_free };
    let new_free: u128 = if input_new_free < ed { 0 } else { input_new_free };

    // --- Lines 809-812 ---
    force_set_balance_imbalance(new_free, old_free);

    // Entire force_set_balance logic verified: no panic possible.
}

// ============================================================================
// force_adjust_total_issuance — ported from balances/src/lib.rs:838-840
//
// let new = match direction {
//     AdjustmentDirection::Increase => old.saturating_add(delta),
//     AdjustmentDirection::Decrease => old.saturating_sub(delta),
// };
//
// saturating_add/sub never panic by definition.
// ============================================================================

/// saturating_add for u128 — faithful to Rust's impl.
pub fn saturating_add_u128(a: u128, b: u128) -> (result: u128)
    ensures
        a as int + b as int <= u128::MAX as int ==> result as int == a as int + b as int,
        a as int + b as int > u128::MAX as int ==> result == u128::MAX,
{
    if a <= u128::MAX - b {
        a + b
    } else {
        u128::MAX
    }
}

/// saturating_sub for u128 — faithful to Rust's impl.
pub fn saturating_sub_u128(a: u128, b: u128) -> (result: u128)
    ensures
        a >= b ==> result == a - b,
        a < b ==> result == 0u128,
{
    if a >= b {
        a - b
    } else {
        0
    }
}

/// Port of force_adjust_total_issuance's arithmetic.
/// direction: 0 = Increase, 1 = Decrease
pub fn force_adjust_total_issuance(old: u128, delta: u128, direction: u8) -> (new: u128)
{
    // --- Lines 838-840 ---
    if direction == 0 {
        saturating_add_u128(old, delta)
    } else {
        saturating_sub_u128(old, delta)
    }
    // No panic possible — saturating ops are always safe.
}

} // verus!
