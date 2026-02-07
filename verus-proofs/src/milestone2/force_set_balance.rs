use vstd::prelude::*;
use crate::milestone2::types::*;

verus! {

// ============================================================================
// Milestone 2: force_set_balance guarded subtraction proof
//
// Source: substrate/frame/balances/src/lib.rs:809-812
//
// The relevant code in force_set_balance:
//
// let old_free = account.free;
// account.free = new_free;
// match old_free.cmp(&new_free) {
//     Ordering::Greater => {
//         // old_free > new_free, so old_free - new_free is safe
//         Self::deposit_event(Event::BalanceSet { who, free: new_free });
//         Ok(NegativeImbalance::new(old_free - new_free))
//     },
//     Ordering::Less => {
//         // new_free > old_free, so new_free - old_free is safe
//         Self::deposit_event(Event::BalanceSet { who, free: new_free });
//         Ok(PositiveImbalance::new(new_free - old_free))
//     },
//     Ordering::Equal => {
//         // No change, no imbalance
//         Ok(())  // simplified
//     },
// }
//
// The critical observation: each subtraction is guarded by a comparison
// that ensures the result is non-negative. Verus checks this automatically.
// ============================================================================

/// Model of the guarded subtraction in force_set_balance.
///
/// This exec function is verified by Verus for no underflow.
/// The comparison guard ensures each subtraction is safe.
pub fn force_set_balance_imbalance(old_free: Balance, new_free: Balance)
    -> (result: Result<(), ()>)
{
    if old_free > new_free {
        // old_free - new_free: safe because old_free > new_free
        let diff = old_free - new_free;
        let _neg = NegativeImbalance { amount: diff };
        Ok(())
    } else if new_free > old_free {
        // new_free - old_free: safe because new_free > old_free
        let diff = new_free - old_free;
        let _pos = PositiveImbalance { amount: diff };
        Ok(())
    } else {
        // old_free == new_free: no imbalance created
        Ok(())
    }
}

/// **THEOREM: force_set_balance subtraction never underflows.**
///
/// The function above is verified by Verus (exec mode) to never have
/// arithmetic underflow. This proof function documents the theorem.
pub proof fn theorem_force_set_balance_no_underflow(
    old_free: Balance,
    new_free: Balance,
)
    ensures
        // If old > new, the difference is representable
        old_free > new_free ==> old_free - new_free >= 0,
        // If new > old, the difference is representable
        new_free > old_free ==> new_free - old_free >= 0,
{
    // Trivially true from the guards.
}

// ============================================================================
// upgrade_accounts loop — uses saturating_inc (no panic)
//
// Source: substrate/frame/balances/src/lib.rs:766-771
//
// for who in who_list {
//     let _ = Self::try_mutate_account(&who, |a, _| {
//         Self::deposit_event(Event::Upgraded { who });
//         upgraded.saturating_inc();  // <-- saturating, never panics
//         Ok(())
//     });
// }
// ============================================================================

/// Model of saturating_inc: saturating addition of 1.
/// If value == u64::MAX, stays at u64::MAX. Never panics.
pub fn saturating_inc(value: u64) -> (result: u64)
    ensures
        value < u64::MAX ==> result == value + 1,
        value == u64::MAX ==> result == u64::MAX,
{
    if value < u64::MAX {
        value + 1
    } else {
        value
    }
}

// ============================================================================
// force_adjust_total_issuance — uses saturating_add/saturating_sub (no panic)
//
// Source: substrate/frame/balances/src/lib.rs:837-840
//
// match direction {
//     AdjustmentDirection::Increase =>
//         TotalIssuance::mutate(|v| *v = v.saturating_add(delta)),
//     AdjustmentDirection::Decrease =>
//         TotalIssuance::mutate(|v| *v = v.saturating_sub(delta)),
// }
// ============================================================================

/// Model of saturating_add for u128. Never panics.
pub fn saturating_add(a: Balance, b: Balance) -> (result: Balance)
    ensures
        a as int + b as int <= u128::MAX as int ==> result == a + b,
        a as int + b as int > u128::MAX as int ==> result == u128::MAX,
{
    if a <= u128::MAX - b {
        a + b
    } else {
        u128::MAX
    }
}

/// Model of saturating_sub for u128. Never panics.
pub fn saturating_sub(a: Balance, b: Balance) -> (result: Balance)
    ensures
        a >= b ==> result == a - b,
        a < b ==> result == 0,
{
    if a >= b {
        a - b
    } else {
        0
    }
}

/// Model of force_adjust_total_issuance dispatch logic.
/// Uses saturating operations — never panics.
pub fn force_adjust_total_issuance_model(
    direction: AdjustmentDirection,
    current_issuance: Balance,
    delta: Balance,
) -> (new_issuance: Balance)
{
    match direction {
        AdjustmentDirection::Increase => saturating_add(current_issuance, delta),
        AdjustmentDirection::Decrease => saturating_sub(current_issuance, delta),
    }
}

// ============================================================================
// burn dispatchable — uses checked_sub with early-return (no panic)
//
// Source: substrate/frame/balances/src/lib.rs:856-874
//
// The burn dispatchable:
//   let amount = reducible.min(value);  // clamp
//   // ... then uses burn_from which is external_body
// ============================================================================

/// Model of min for Balance. Pure, no panic.
pub fn balance_min(a: Balance, b: Balance) -> (result: Balance)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a <= b { a } else { b }
}

} // verus!
