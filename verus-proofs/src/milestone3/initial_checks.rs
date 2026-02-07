use vstd::prelude::*;
use crate::milestone3::types::*;

verus! {

// ============================================================================
// Executive::initial_checks — ported from executive/src/lib.rs:681-692
//
// Panic point #3: Parent hash mismatch
//
// fn initial_checks(block: &Block) {
//     let header = block.header();
//     let n = *header.number();
//     assert!(
//         n > Zero::zero()
//             && <frame_system::Pallet<System>>::block_hash(n - One::one())
//                 == *header.parent_hash(),
//         "Parent hash should be valid.",
//     );
// }
// ============================================================================

/// **THEOREM: initial_checks does not panic given valid parent hash.**
///
/// Preconditions:
///   - header.number > 0 (not genesis)
///   - stored_block_hash(header.number - 1) == header.parent_hash
///
/// These correspond to panic inventory items #1 and #3.
pub proof fn initial_checks_no_panic(header: &Header)
    requires
        // Block number > 0 (genesis not executed via execute_block)
        header.number > 0u32,
        // Parent hash matches stored hash of previous block
        stored_block_hash((header.number - 1) as u32) == header.parent_hash,
    ensures
        true,
{
    // Model of the assert! in initial_checks:
    //   assert!(n > 0 && block_hash(n-1) == parent_hash)
    assert(header.number > 0u32);

    // n - 1 is safe because n > 0, and (header.number - 1) as u32 is well-defined
    // since header.number > 0 means header.number >= 1
    assert(stored_block_hash((header.number - 1) as u32) == header.parent_hash);
}

} // verus!
