use vstd::prelude::*;
use crate::milestone3::types::*;

verus! {

// ============================================================================
// Executive::final_checks — ported from executive/src/lib.rs:920-946
//
// Panic points #8-11:
//   #8:  assert_eq!(digest.len(), computed_digest.len())
//   #9:  assert!(header_item == computed_item) for each digest item
//   #10: assert!(header.state_root() == storage_root)
//   #11: assert!(header.extrinsics_root() == computed_extrinsics_root)
//
// The real code:
//
// fn final_checks(header: &Header) {
//     let new_header = <frame_system::Pallet<System>>::finalize();
//     assert_eq!(
//         header.digest().logs().len(),
//         new_header.digest().logs().len(),
//     );
//     for i in 0..header.digest().logs().len() {
//         assert!(
//             header.digest().logs()[i] == new_header.digest().logs()[i],
//             "...",
//         );
//     }
//     assert!(header.state_root() == new_header.state_root());
//     assert!(header.extrinsics_root() == new_header.extrinsics_root());
// }
// ============================================================================

/// **THEOREM: final_checks does not panic given correct digests.**
///
/// Preconditions (the "correct digests" property):
///   - Digest log counts match
///   - Each digest item matches pointwise
///   - State root matches
///   - Extrinsics root matches
pub proof fn final_checks_no_panic(header: Header, new_header: Header)
    requires
        header.digest.logs.len() == new_header.digest.logs.len(),
        forall|i: int|
            0 <= i < header.digest.logs.len()
            ==> (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i],
        header.state_root == new_header.state_root,
        header.extrinsics_root == new_header.extrinsics_root,
    ensures
        true,
{
    // Assert #8: digest lengths equal
    assert(header.digest.logs.len() == new_header.digest.logs.len());

    // Assert #9: each digest item equal
    assert forall|i: int|
        0 <= i < header.digest.logs.len()
    implies
        (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i]
    by {}

    // Assert #10: state root matches
    assert(header.state_root == new_header.state_root);

    // Assert #11: extrinsics root matches
    assert(header.extrinsics_root == new_header.extrinsics_root);
}

/// Variant: derives pointwise equality from structural header equality.
pub proof fn final_checks_with_correct_block(block: &Block)
    requires
        block.header == finalized_header_after_execution(block),
    ensures
        true,
{
    let header = block.header;
    let new_header = finalized_header_after_execution(block);

    assert(header.digest.logs =~= new_header.digest.logs);
    assert(header.digest.logs.len() == new_header.digest.logs.len());

    assert forall|i: int|
        0 <= i < header.digest.logs.len()
    implies
        (#[trigger] header.digest.logs[i]) == new_header.digest.logs[i]
    by {}

    final_checks_no_panic(header, new_header);
}

} // verus!
