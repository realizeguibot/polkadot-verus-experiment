use vstd::prelude::*;
use crate::model_digest::*;
use crate::model_header::*;

verus! {

/// Model of `Executive::final_checks`.
///
/// In the real code (executive/src/lib.rs:920-946):
///   1. Calls System::finalize() → produces `new_header`
///   2. assert_eq!(header.digest.logs.len(), new_header.digest.logs.len())
///   3. For each (header_item, computed_item): assert!(header_item == computed_item)
///   4. assert!(header.state_root == new_header.state_root)
///   5. assert!(header.extrinsics_root == new_header.extrinsics_root)
///
/// Each of these assert!/assert_eq! will panic if the condition is false.
///
/// THEOREM: Given the "correct digests" precondition — that the block header
/// matches the finalized header produced by execution — final_checks does not panic.
///
/// This is modeled as a proof function: if we can verify it, then no panic
/// can occur under the stated preconditions.

pub proof fn final_checks_no_panic(header: Header, new_header: Header)
    requires
        // "Correct digests" precondition:
        // The block's header matches what execution computed.

        // 1. Digest log count matches
        header.digest.logs.len() == new_header.digest.logs.len(),

        // 2. Each digest item matches
        forall|i: int|
            0 <= i < header.digest.logs.len()
            ==> (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i],

        // 3. State root matches
        header.state_root == new_header.state_root,

        // 4. Extrinsics root matches
        header.extrinsics_root == new_header.extrinsics_root,
    ensures
        // The function completes without any assertion failure (no panic).
        // In Verus, if this proof function verifies, it means all the
        // assertions below are satisfiable under the preconditions.
        true,
{
    // Step 1: assert_eq!(header.digest().logs().len(), new_header.digest().logs().len())
    // This corresponds to line 926-930 in executive/src/lib.rs
    assert(header.digest.logs.len() == new_header.digest.logs.len());

    // Step 2: for each item, assert!(header_item == computed_item)
    // This corresponds to lines 931-935 in executive/src/lib.rs
    // We prove this holds for all indices in the digest.
    assert forall|i: int|
        0 <= i < header.digest.logs.len()
    implies
        (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i]
    by {
        // Directly from the precondition.
    }

    // Step 3: assert!(header.state_root() == storage_root)
    // Line 940 in executive/src/lib.rs
    assert(header.state_root == new_header.state_root);

    // Step 4: assert!(header.extrinsics_root() == new_header.extrinsics_root())
    // Lines 942-945 in executive/src/lib.rs
    assert(header.extrinsics_root == new_header.extrinsics_root);
}

/// Stronger version: if the header IS the finalized header, final_checks is trivially safe.
/// This models the case where the block proposer constructed the header correctly.
proof fn final_checks_with_correct_block(block: Block)
    requires
        // The block header exactly equals the finalized header after execution
        block.header == finalized_header_after_execution(&block),
    ensures
        true,
{
    let header = block.header;
    let new_header = finalized_header_after_execution(&block);

    // Since header == new_header, all fields are equal.
    assert(header.digest.logs.len() == new_header.digest.logs.len());
    assert(header.state_root == new_header.state_root);
    assert(header.extrinsics_root == new_header.extrinsics_root);

    // Each digest item is equal
    assert forall|i: int|
        0 <= i < header.digest.logs.len()
    implies
        (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i]
    by {
        // header == new_header, so header.digest == new_header.digest,
        // so header.digest.logs == new_header.digest.logs,
        // so pointwise equality holds.
    }

    // Delegate to the main theorem
    final_checks_no_panic(header, new_header);
}

/// Proof that initial_checks doesn't panic given correct parent hash.
///
/// In real code (executive/src/lib.rs:681-691):
///   assert!(n > 0 && block_hash(n - 1) == header.parent_hash)
///
/// We model block_hash as an uninterpreted function.
pub uninterp spec fn stored_block_hash(n: u32) -> HashOutput;

proof fn initial_checks_no_panic(header: Header)
    requires
        // Block number must be > 0 (genesis block is not executed via execute_block)
        header.number > 0u32,
        // Parent hash in the header must match the stored hash of the previous block
        stored_block_hash((header.number - 1) as u32) == header.parent_hash,
    ensures
        true,
{
    // The assert in initial_checks:
    //   assert!(n > 0 && block_hash(n - 1) == parent_hash)
    assert(header.number > 0u32);
    assert(stored_block_hash((header.number - 1) as u32) == header.parent_hash);
}

} // verus!
