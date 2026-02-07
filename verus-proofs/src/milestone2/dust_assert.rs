use vstd::prelude::*;
use crate::milestone2::types::*;

verus! {

// ============================================================================
// Milestone 2: Dust-check defensive assert tautology proof
//
// Source: substrate/frame/balances/src/lib.rs:1130-1143
//
// This is the highest-value single proof in Milestone 2. The defensive
// assert at lib.rs:1138 is called by ALL transfer/mutation paths via
// `try_mutate_account`. If this assert ever fires, balances are broken.
//
// The code structure (simplified):
//
// fn try_mutate_account<R>(
//     who: &T::AccountId,
//     f: impl FnOnce(&mut AccountData<T::Balance>, bool) -> Result<R, DispatchError>,
// ) -> Result<R, DispatchError> {
//     ...
//     let ed = T::ExistentialDeposit::get();
//     let result = f(&mut account, is_new);
//     if account.free < ed && account.reserved.is_zero() {
//         // Dust: account below ED with no reserved balance → kill it
//         account.free = Zero::zero();
//     } else {
//         // NOT dust — the defensive assert:
//         assert!(
//             account.free.is_zero() ||
//             account.free >= ed ||
//             !account.reserved.is_zero(),
//             "... defensive message ..."
//         );
//     }
//     ...
// }
// ============================================================================

/// The condition checked in the if-branch (dust detection).
/// If this is true, we're in the if-branch and the account gets killed.
pub open spec fn is_dust(free: Balance, reserved: Balance, ed: Balance) -> bool {
    free < ed && reserved == 0
}

/// The assertion in the else-branch (defensive check).
/// This is what's checked by the `assert!` at lib.rs:1138.
pub open spec fn defensive_assert_condition(free: Balance, reserved: Balance, ed: Balance) -> bool {
    free == 0 || free >= ed || reserved != 0
}

/// **THEOREM: The defensive assert in try_mutate_account is a tautology.**
///
/// Given:
///   - ed > 0 (from integrity_test)
///   - We are in the else-branch: !(free < ed && reserved == 0)
///
/// Prove:
///   free == 0 || free >= ed || reserved != 0
///
/// Proof by case analysis:
///   The else-branch condition !(free < ed && reserved == 0) means:
///     free >= ed ∨ reserved != 0
///   (by De Morgan: ¬(A ∧ B) ≡ ¬A ∨ ¬B, where A = free < ed, B = reserved == 0)
///
///   Case 1: free >= ed → middle disjunct of the assert holds ✓
///   Case 2: reserved != 0 → right disjunct of the assert holds ✓
///   Case 3: free >= ed ∧ reserved != 0 → both middle and right hold ✓
///
///   Note: the free == 0 case is subsumed:
///     If free == 0 and ed > 0, then free < ed, so we'd need reserved != 0
///     to be in the else-branch. The left disjunct (free == 0) and right
///     disjunct (reserved != 0) both hold.
pub proof fn theorem_dust_assert_is_tautology(
    free: Balance,
    reserved: Balance,
    ed: Balance,
)
    requires
        // Existential deposit is positive (from integrity_test)
        ed > 0,
        // We are in the else-branch of the dust check
        !is_dust(free, reserved, ed),
    ensures
        // The defensive assert condition always holds
        defensive_assert_condition(free, reserved, ed),
{
    // Expand the else-branch condition:
    // !is_dust(free, reserved, ed)
    // ≡ !(free < ed && reserved == 0)
    // ≡ free >= ed ∨ reserved != 0  (De Morgan)

    if free >= ed {
        // Case 1: free >= ed → middle disjunct holds
        assert(defensive_assert_condition(free, reserved, ed));
    } else {
        // Case 2: free < ed, so from ¬(free < ed ∧ reserved == 0),
        // we must have reserved != 0 → right disjunct holds
        assert(reserved != 0u128);
        assert(defensive_assert_condition(free, reserved, ed));
    }
}

/// Variant: prove it also for the case where free == 0.
/// This is the "dusted" case where free was set to zero.
pub proof fn theorem_dust_assert_zero_free(
    reserved: Balance,
    ed: Balance,
)
    requires
        ed > 0,
        !is_dust(0, reserved, ed),
    ensures
        defensive_assert_condition(0, reserved, ed),
{
    // free == 0 < ed (since ed > 0), so !(free < ed && reserved == 0)
    // requires reserved != 0.
    // defensive_assert_condition(0, reserved, ed) =
    //   0 == 0 || 0 >= ed || reserved != 0
    //   = true || ... = true
    assert(0u128 == 0u128);
    assert(defensive_assert_condition(0, reserved, ed));
}

/// **THEOREM: The complete try_mutate_account dust logic never panics.**
///
/// Models the full if/else branching:
///   if is_dust: account.free = 0 (no panic, just an assignment)
///   else: assert!(defensive_assert_condition) — proven tautology above
pub proof fn theorem_try_mutate_account_no_panic(
    free: Balance,
    reserved: Balance,
    ed: Balance,
)
    requires
        ed > 0,
{
    if is_dust(free, reserved, ed) {
        // In the if-branch: account.free = Zero::zero()
        // This is just an assignment, never panics.
        // After assignment, free becomes 0 — no assert is checked.
    } else {
        // In the else-branch: the defensive assert
        theorem_dust_assert_is_tautology(free, reserved, ed);
    }
}

} // verus!
