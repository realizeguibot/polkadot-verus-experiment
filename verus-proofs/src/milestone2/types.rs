use vstd::prelude::*;

verus! {

// ============================================================================
// Concrete types for Milestone 2: pallet_balances panic-freedom
//
// These mirror actual types from substrate/frame/balances/src/lib.rs
// and related frame_support types used in the dispatchable call chain.
// ============================================================================

/// Balance type — u128 for Asset Hub.
/// Mirrors: <T as pallet_balances::Config>::Balance = u128
pub type Balance = u128;

/// Account data for the balances pallet.
/// Mirrors: pallet_balances::AccountData<Balance>
///
/// Source: substrate/frame/balances/src/types.rs
pub struct AccountData {
    pub free: Balance,
    pub reserved: Balance,
    pub frozen: Balance,
}

/// Existential deposit — minimum balance to keep an account alive.
/// For Asset Hub this is a small nonzero value.
/// Invariant: ed > 0 (enforced by pallet_balances::integrity_test)
pub struct BalancesConfig {
    pub existential_deposit: Balance,
}

/// Dispatch result type — all dispatchables return this.
/// Mirrors: frame_support::dispatch::DispatchResult = Result<(), DispatchError>
pub enum DispatchError {
    Module(u8),
    Arithmetic(u8),
    Token(u8),
    Other,
}

pub type DispatchResult = Result<(), DispatchError>;

/// Imbalance types — created by balance mutations.
/// We model them as simple wrappers since we only care about
/// the arithmetic safety of their construction.
pub struct PositiveImbalance {
    pub amount: Balance,
}

pub struct NegativeImbalance {
    pub amount: Balance,
}

/// Adjustment direction for force_adjust_total_issuance.
/// Mirrors: pallet_balances::AdjustmentDirection
pub enum AdjustmentDirection {
    Increase,
    Decrease,
}

/// ExistenceRequirement — used by legacy transfer functions.
pub enum ExistenceRequirement {
    KeepAlive,
    AllowDeath,
}

/// Preservation — modern version of ExistenceRequirement.
pub enum Preservation {
    Expendable,
    Protect,
    Preserve,
}

} // verus!
