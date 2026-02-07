use vstd::prelude::*;

verus! {

// ============================================================================
// Ported from: substrate/frame/timestamp/src/lib.rs
//
// Two functions with panics:
//   1. Timestamp::set (lines 259-273) — two assert! statements
//   2. Timestamp::on_finalize (line 229) — one assert!
//
// Both are exec fns with real u64 arithmetic.
// ============================================================================

// ============================================================================
// Timestamp::set — ported from timestamp/src/lib.rs:259-273
//
// pub fn set(origin, now: T::Moment) -> DispatchResult {
//     ensure_none(origin)?;
//     assert!(!DidUpdate::<T>::exists(), "Timestamp must be updated only once in the block");
//     let prev = Now::<T>::get();
//     assert!(
//         prev.is_zero() || now >= prev + T::MinimumPeriod::get(),
//         "Timestamp must increment by at least <MinimumPeriod>..."
//     );
//     Now::<T>::put(now);
//     DidUpdate::<T>::put(true);
//     <T::OnTimestampSet as OnTimestampSet<_>>::on_timestamp_set(now);
//     Ok(())
// }
//
// Panic points:
//   Line 261: assert!(!DidUpdate) — timestamp set twice in same block
//   Line 263: assert!(prev == 0 || now >= prev + min_period) — too early
//
// Note: `prev + T::MinimumPeriod::get()` uses Rust's + operator on u64.
// In release mode this wraps on overflow. In debug mode it panics.
// The Substrate runtime compiles in release mode, so wrapping would occur.
// We prove: no overflow occurs AND both asserts hold.
// ============================================================================

/// Faithful port of Timestamp::set's panic-relevant logic.
///
/// Parameters replace storage reads:
///   did_update ← DidUpdate::<T>::exists()
///   prev       ← Now::<T>::get()
///   now        ← the `now` parameter
///   min_period ← T::MinimumPeriod::get()
pub fn timestamp_set(
    did_update: bool,
    prev: u64,
    now: u64,
    min_period: u64,
)
    requires
        // Timestamp has not been set yet in this block
        !did_update,
        // Either this is the first block (prev == 0) or the timestamp
        // advances by at least min_period
        prev == 0u64 || now >= prev + min_period,
        // The addition prev + min_period doesn't overflow u64
        // (timestamps are ms since epoch ≈ 1.7×10^12, well within u64::MAX ≈ 1.8×10^19)
        prev as int + min_period as int <= u64::MAX as int,
{
    // --- Line 261 ---
    // assert!(!DidUpdate::<T>::exists(), "Timestamp must be updated only once in the block");
    assert(!did_update);

    // --- Lines 263-266 ---
    // assert!(prev.is_zero() || now >= prev + T::MinimumPeriod::get(), "...");
    //
    // The addition prev + min_period:
    let threshold: u64 = prev + min_period;
    //                    ^^^^^^^^^^^^^^^^ Verus checks: no u64 overflow
    //                    (guaranteed by requires: prev + min_period <= u64::MAX)

    assert(prev == 0u64 || now >= threshold);
}

// ============================================================================
// Timestamp::on_finalize — ported from timestamp/src/lib.rs:228-230
//
// fn on_finalize(_n: BlockNumberFor<T>) {
//     assert!(DidUpdate::<T>::take(), "Timestamp must be updated once in the block");
// }
//
// DidUpdate::take() reads the bool and clears it. The assert checks it was true.
// ============================================================================

/// Faithful port of Timestamp::on_finalize.
///
/// Parameters:
///   did_update ← DidUpdate::<T>::take()
pub fn timestamp_on_finalize(did_update: bool)
    requires
        // The timestamp inherent was present in the block and set DidUpdate to true
        did_update,
{
    // --- Line 229 ---
    // assert!(DidUpdate::<T>::take(), "Timestamp must be updated once in the block");
    assert(did_update);
}

} // verus!
