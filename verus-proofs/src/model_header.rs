use vstd::prelude::*;
use crate::model_digest::*;

verus! {

/// Extrinsic inclusion mode — determined by whether multi-block migrations are ongoing.
/// Mirrors: sp_runtime::ExtrinsicInclusionMode
pub ghost enum ExtrinsicInclusionMode {
    AllExtrinsics,
    OnlyInherents,
}

/// Model of a block extrinsic (opaque for our purposes).
/// We only care about whether it's an inherent or not, and whether
/// dispatch succeeds or fails.
pub ghost struct Extrinsic {
    pub is_inherent: bool,
    pub dispatch_succeeds: bool,
}

/// Model of a complete block.
/// Mirrors: sp_runtime::generic::Block<Header, Extrinsic>
pub ghost struct Block {
    pub header: Header,
    pub extrinsics: Seq<Extrinsic>,
}

impl Block {
    /// Count of inherent extrinsics (ghost/spec).
    pub open spec fn inherent_count(&self) -> nat {
        self.extrinsics.filter(|e: Extrinsic| e.is_inherent).len()
    }

    /// Inherents are contiguous at the start of the extrinsic list.
    /// This is a fundamental block validity invariant maintained by the block builder.
    pub open spec fn inherents_contiguous_at_start(&self) -> bool {
        self.inherents_contiguous_with_boundary(self.inherent_boundary())
    }

    /// The boundary index: first k items are inherent, rest are not.
    pub uninterp spec fn inherent_boundary(&self) -> nat;

    /// The partition property parameterized by a boundary k.
    pub open spec fn inherents_contiguous_with_boundary(&self, k: nat) -> bool {
        &&& k <= self.extrinsics.len()
        &&& (forall|i: int| 0 <= i < k ==> (#[trigger] self.extrinsics[i]).is_inherent)
        &&& (forall|i: int| k <= i < self.extrinsics.len() as int
                ==> !(#[trigger] self.extrinsics[i]).is_inherent)
    }

    /// All extrinsic dispatches succeed (no errors).
    /// In practice this is guaranteed by the block builder and validator.
    pub open spec fn all_dispatches_succeed(&self) -> bool {
        forall|i: int| 0 <= i < self.extrinsics.len() as int
            ==> (#[trigger] self.extrinsics[i]).dispatch_succeeds
    }

    /// The block is well-formed for execution in a given mode.
    pub open spec fn well_formed(&self, mode: ExtrinsicInclusionMode) -> bool {
        &&& self.inherents_contiguous_at_start()
        &&& self.all_dispatches_succeed()
        &&& (mode == ExtrinsicInclusionMode::OnlyInherents ==>
                forall|i: int| 0 <= i < self.extrinsics.len() as int
                    ==> (#[trigger] self.extrinsics[i]).is_inherent)
    }
}

/// Spec function: the "new_header" that System::finalize() would produce
/// after executing all extrinsics and hooks.
///
/// This is the core abstraction: we don't model _how_ the runtime computes
/// the finalized header (that involves all 40+ pallets, storage, etc.).
/// Instead we treat it as an opaque oracle function, and the "correct digests"
/// precondition says the block's header matches this oracle output.
pub uninterp spec fn finalized_header_after_execution(block: &Block) -> Header;

} // verus!
