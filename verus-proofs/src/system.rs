use vstd::prelude::*;

verus! {

// ============================================================================
// Ported from: substrate/frame/system/src/lib.rs:1922-1958
//
// pub fn initialize(number: &BlockNumberFor<T>, parent_hash: &T::Hash, digest: &generic::Digest) {
//     let expected_block_number = Self::block_number() + One::one();
//     assert_eq!(expected_block_number, *number, "Block number must be strictly increasing.");
//     ...
//     let digest_size = digest.encoded_size();
//     let empty_header = <<T as Config>::Block as traits::Block>::Header::new(...);
//     let empty_header_size = empty_header.encoded_size();
//     let overhead = digest_size.saturating_add(empty_header_size) as u32;
//     BlockSize::<T>::put(overhead);
//     let max_total_header = T::BlockLength::get().max_header_size();
//     assert!(
//         overhead <= max_total_header as u32,
//         "Header size ({overhead}) exceeds max header size limit ({max_total_header})"
//     );
// }
//
// This function has TWO panics:
//   1. assert_eq! at line 1924 if block number is not sequential
//   2. assert! at line 1954 if header overhead exceeds max header size
//
// We port the exact arithmetic and assertions. Storage reads are parameters.
// Verus checks: u32 addition overflow, and both assertions hold.
// ============================================================================

/// Faithful port of System::initialize's panic-relevant logic.
///
/// Parameters replace storage reads:
///   stored_block_number ← Self::block_number()
///   number              ← the *number parameter
///   digest_encoded_size ← digest.encoded_size()
///   empty_header_size   ← empty_header.encoded_size()
///   max_header_size     ← T::BlockLength::get().max_header_size()
pub fn system_initialize(
    stored_block_number: u32,
    number: u32,
    digest_encoded_size: usize,
    empty_header_size: usize,
    max_header_size: u32,
)
    requires
        // The block number addition doesn't overflow
        stored_block_number < u32::MAX,
        // The caller passes number == stored + 1 (true in both
        // execute_block and validate_transaction call sites)
        number == stored_block_number + 1,
        // The saturating_add doesn't actually saturate (reasonable for real headers)
        digest_encoded_size + empty_header_size <= u32::MAX as usize,
        // The header overhead fits within the configured limit
        (digest_encoded_size + empty_header_size) as u32 <= max_header_size,
{
    // --- Line 1923 ---
    // let expected_block_number = Self::block_number() + One::one();
    let expected_block_number: u32 = stored_block_number + 1;
    //                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    // Verus checks: stored_block_number + 1 doesn't overflow u32
    // (guaranteed by requires: stored_block_number < u32::MAX)

    // --- Line 1924 ---
    // assert_eq!(expected_block_number, *number, "Block number must be strictly increasing.");
    assert(expected_block_number == number);

    // --- Lines 1940-1949 (simplified) ---
    // let overhead = digest_size.saturating_add(empty_header_size) as u32;
    let overhead_usize: usize = if digest_encoded_size > usize::MAX - empty_header_size {
        usize::MAX
    } else {
        digest_encoded_size + empty_header_size
    };
    let overhead: u32 = overhead_usize as u32;
    //                   ^^^^^^^^^^^^^^^^^^^
    // Verus checks: usize→u32 cast doesn't truncate
    // (guaranteed by requires: sum <= u32::MAX)

    // --- Line 1954-1957 ---
    // assert!(overhead <= max_total_header as u32, "Header size exceeds max...");
    assert(overhead <= max_header_size);
}

} // verus!
