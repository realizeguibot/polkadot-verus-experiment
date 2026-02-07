# Verus Verification Plan: Panic-Freedom of Asset Hub STF Given Correct Digests

## Goal

Formally prove with [Verus](https://github.com/verus-lang/verus) that the
**State Transition Function (STF)** of **Polkadot Asset Hub** — specifically
`Executive::execute_block` — **does not panic** when invoked with a block whose
header digests are *correct* (i.e., consistent with the actual execution
outcome).

---

## 1. What "Correct Digests" Means

The block header contains a `Digest` (a `Vec<DigestItem>`), which includes:

| Variant | Direction | Meaning |
|---------|-----------|---------|
| `PreRuntime(engine_id, data)` | consensus → runtime | Slot/authority info (e.g., Aura slot) |
| `Consensus(engine_id, data)` | runtime → consensus | Consensus-relevant messages |
| `Seal(engine_id, signature)` | consensus → runtime | Block signature (stripped before execution) |
| `RuntimeEnvironmentUpdated` | runtime → runtime | Code or heap-pages change |

**"Correct digests"** means:

1. The `PreRuntime` items in the header are decodable by the consensus engine
   (Aura for Asset Hub) and refer to a valid slot.
2. After full block execution the runtime-computed digest logs **match exactly**
   the digest logs in the provided header (this is what `final_checks` asserts).
3. The `state_root` in the header equals the post-execution storage trie root.
4. The `extrinsics_root` equals the Merkle root of the extrinsic list.
5. The `parent_hash` equals the hash of the previous block header.

Formally, the precondition is:

```
requires
    header.digest == computed_digest_after_execution(state, extrinsics),
    header.state_root == computed_state_root_after_execution(state, extrinsics),
    header.extrinsics_root == merkle_root(extrinsics),
    header.parent_hash == hash(parent_header),
```

---

## 2. Anatomy of the STF — Panic Points

### 2.1 `Executive::execute_block` (executive/src/lib.rs:695)

```
execute_block(block)
  ├─ initialize_block(header)
  │    ├─ extract_pre_digest(header)          // iterates digest, no panic
  │    └─ initialize_block_impl(number, parent_hash, digests)
  │         ├─ System::reset_events()
  │         ├─ System::initialize(number, parent_hash, digest)
  │         ├─ <on_runtime_upgrade>           // ⚠ can panic if migration fails
  │         └─ <on_initialize hooks>          // ⚠ pallet hooks can panic
  ├─ initial_checks(header)
  │    └─ assert!(parent_hash == System::parent_hash())   // ⚠ PANIC if wrong parent
  ├─ apply_extrinsics(mode, extrinsics, apply_fn)
  │    ├─ decode each extrinsic               // ⚠ PANIC on decode failure
  │    ├─ inherent ordering check             // ⚠ PANIC on mis-ordered inherents
  │    ├─ mode check                          // ⚠ PANIC if non-inherent in OnlyInherents mode
  │    └─ apply_extrinsic → dispatch          // ⚠ PANIC on dispatch error
  ├─ inherents_applied()
  ├─ note_finished_extrinsics()
  ├─ PostTransactions hook
  ├─ on_idle_hook                             // ⚠ pallet hooks can panic
  ├─ on_finalize_hook                         // ⚠ pallet hooks can panic
  └─ final_checks(header)
       ├─ assert_eq!(digest.len())            // ⚠ PANIC if digest count wrong
       ├─ assert_eq!(each digest item)        // ⚠ PANIC if digest item wrong
       ├─ assert_eq!(state_root)              // ⚠ PANIC if state root wrong
       └─ assert_eq!(extrinsics_root)         // ⚠ PANIC if extrinsics root wrong
```

### 2.2 Categorized Panic Sources

| # | Source | Location | Under "correct digests" assumption |
|---|--------|----------|-----------------------------------|
| 1 | `final_checks` assert_eq on digests | executive/lib.rs:920-946 | **Eliminated** by precondition |
| 2 | `final_checks` assert_eq on state_root | same | **Eliminated** by precondition |
| 3 | `final_checks` assert_eq on extrinsics_root | same | **Eliminated** by precondition |
| 4 | `initial_checks` parent hash | executive/lib.rs | **Eliminated** by precondition |
| 5 | Extrinsic decode failure | apply_extrinsics | **Must prove**: valid encoding |
| 6 | Inherent ordering violation | apply_extrinsics | **Must prove**: block builder invariant |
| 7 | Non-inherent in OnlyInherents mode | apply_extrinsics | **Must prove**: consistency |
| 8 | Extrinsic dispatch error | do_apply_extrinsic | **Must prove or scope out** |
| 9 | Pallet on_initialize hooks | various pallets | **Must scope out** (external_body) |
| 10 | Pallet on_finalize hooks | various pallets | **Must scope out** (external_body) |
| 11 | Pallet on_idle hooks | various pallets | **Must scope out** (external_body) |
| 12 | Runtime upgrade migrations | on_runtime_upgrade | **Must scope out** (external_body) |
| 13 | Arithmetic overflow anywhere | throughout | **Must prove** case by case |

---

## 3. Verification Architecture

### 3.1 Trust Boundaries

```
┌──────────────────────────────────────────────────────┐
│                    VERIFIED (Verus)                   │
│                                                      │
│  execute_block_model()                               │
│    ├─ extract_pre_digest()                           │
│    ├─ initial_checks_model()                         │
│    ├─ apply_extrinsics_model()                       │
│    └─ final_checks_model()                           │
│                                                      │
│  Data structures:                                    │
│    Digest, DigestItem, Header, Block (modeled)       │
│                                                      │
├──────────────────────────────────────────────────────┤
│           TRUST BOUNDARY (external_body)             │
├──────────────────────────────────────────────────────┤
│                                                      │
│  UNVERIFIED (trusted specifications):                │
│    - Storage read/write (sp_io host functions)       │
│    - All 40+ pallet hooks (on_init, on_finalize)     │
│    - SCALE codec encode/decode                       │
│    - Hashing (BlakeTwo256)                           │
│    - Extrinsic dispatch (per-pallet logic)           │
│    - Trie/Merkle root computation                    │
│    - Aura consensus logic                            │
│    - Cumulus parachain-system validate_block          │
│                                                      │
└──────────────────────────────────────────────────────┘
```

### 3.2 What We Prove

Given the preconditions ("correct digests"), we prove that
`execute_block_model` — a Verus model of the real `Executive::execute_block` —
**never panics** (all assertions hold, no arithmetic overflow, no unwrap on
None, no out-of-bounds indexing).

### 3.3 What We Assume (TCB)

- Pallet hooks (`on_initialize`, `on_finalize`, `on_idle`) do not panic →
  modeled as `external_body` with `ensures !panicked`.
- Storage host functions behave correctly.
- SCALE codec: `decode(encode(x)) == Some(x)` for well-typed values.
- The Rust compiler and WASM compilation are correct.
- Verus and Z3 are sound.

---

## 4. Implementation Plan

### Phase 0: Tooling Setup (Week 1)

1. **Install Verus** from source (requires nightly Rust).
2. Set up a standalone Cargo project inside `polkadot-verus-experiment/`
   that depends on Verus and can import selected types.
3. Verify Verus works with a trivial `no_std` proof.
4. **Key risk**: Verus requires its own `verus!` macro and custom Rust toolchain.
   Confirm it can coexist with Substrate's build system, or plan to model the
   code in a separate crate.

```
polkadot-verus-experiment/
├── polkadot-sdk/              # reference (read-only)
├── runtimes/                  # reference (read-only)
├── verus-proofs/              # NEW: our Verus verification crate
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── model_digest.rs    # Verus model of Digest types
│       ├── model_header.rs    # Verus model of Header
│       ├── model_executive.rs # Verus model of execute_block
│       └── proofs/
│           ├── digest_consistency.rs
│           ├── final_checks.rs
│           ├── apply_extrinsics.rs
│           └── panic_freedom.rs
└── PLAN.md
```

### Phase 1: Model Core Data Types (Week 2)

Port/model the following types in Verus-annotated Rust:

```rust
verus! {

// ConsensusEngineId
pub type ConsensusEngineId = [u8; 4];

// DigestItem — simplified model
pub enum DigestItem {
    PreRuntime(ConsensusEngineId, Vec<u8>),
    Consensus(ConsensusEngineId, Vec<u8>),
    Seal(ConsensusEngineId, Vec<u8>),
    Other(Vec<u8>),
    RuntimeEnvironmentUpdated,
}

// Digest
pub struct Digest {
    pub logs: Vec<DigestItem>,
}

// Header (parameterized by hash output type)
pub struct Header {
    pub parent_hash: [u8; 32],
    pub number: u32,
    pub state_root: [u8; 32],
    pub extrinsics_root: [u8; 32],
    pub digest: Digest,
}

} // verus!
```

**Proof obligation**: Model `extract_pre_digest` and prove it never panics:
```rust
verus! {
fn extract_pre_digest(header: &Header) -> (result: Digest)
    ensures
        forall|i: int| 0 <= i < result.logs.len() ==>
            result.logs[i].is_PreRuntime(),
{
    let mut digest = Digest { logs: Vec::new() };
    let mut idx: usize = 0;
    while idx < header.digest.logs.len()
        invariant
            idx <= header.digest.logs.len(),
            forall|j: int| 0 <= j < digest.logs.len() ==>
                digest.logs[j].is_PreRuntime(),
    {
        if header.digest.logs[idx].is_pre_runtime() {
            digest.logs.push(header.digest.logs[idx].clone());
        }
        idx = idx + 1;  // Verus checks: idx + 1 <= usize::MAX
    }
    digest
}
} // verus!
```

### Phase 2: Model `final_checks` and Prove Safety (Week 3)

This is the most direct target. `final_checks` has three `assert_eq!` calls that
panic. Under our "correct digests" precondition, they must hold.

```rust
verus! {

// Spec function: what the runtime computes
spec fn computed_digest(/* execution state */) -> Digest;
spec fn computed_state_root(/* execution state */) -> [u8; 32];
spec fn computed_extrinsics_root(extrinsics: &[Extrinsic]) -> [u8; 32];

fn final_checks_model(
    header: &Header,
    new_header: &Header,  // computed by finalize()
)
    requires
        // "correct digests" precondition
        header.digest.logs.len() == new_header.digest.logs.len(),
        forall|i: int| 0 <= i < header.digest.logs.len() ==>
            header.digest.logs[i] == new_header.digest.logs[i],
        header.state_root == new_header.state_root,
        header.extrinsics_root == new_header.extrinsics_root,
    // No ensures needed — we just prove this doesn't panic
{
    // Digest length check
    assert(header.digest.logs.len() == new_header.digest.logs.len());

    // Digest item-by-item check
    let mut i: usize = 0;
    while i < header.digest.logs.len()
        invariant
            i <= header.digest.logs.len(),
            forall|j: int| 0 <= j < i as int ==>
                header.digest.logs[j] == new_header.digest.logs[j],
    {
        assert(header.digest.logs[i] == new_header.digest.logs[i]);
        i = i + 1;
    }

    // State root check
    assert(header.state_root == new_header.state_root);

    // Extrinsics root check
    assert(header.extrinsics_root == new_header.extrinsics_root);
}

} // verus!
```

### Phase 3: Model `apply_extrinsics` Loop (Week 4-5)

The extrinsic application loop is the most complex part. Key properties:

1. **Decode cannot fail** → precondition: all extrinsics are well-encoded.
2. **Inherent ordering** → precondition: inherents come first (block builder invariant).
3. **No panic from dispatch** → model dispatch as `external_body` returning `Result`.

```rust
verus! {

pub enum ExtrinsicInclusionMode { AllExtrinsics, OnlyInherents }

// Model of the extrinsic application loop
fn apply_extrinsics_model(
    mode: ExtrinsicInclusionMode,
    extrinsics: &Vec<Extrinsic>,
    inherent_count: usize,  // ghost: number of inherent extrinsics
)
    requires
        // All extrinsics are decodable (well-formed block)
        // Inherents are contiguous at the start
        inherent_count <= extrinsics.len(),
        forall|i: int| 0 <= i < inherent_count as int ==>
            extrinsics[i].is_inherent(),
        forall|i: int| inherent_count as int <= i < extrinsics.len() ==>
            !extrinsics[i].is_inherent(),
        // If mode is OnlyInherents, no non-inherent extrinsics
        mode == ExtrinsicInclusionMode::OnlyInherents ==>
            inherent_count == extrinsics.len(),
{
    let mut first_non_inherent_idx: usize = 0;
    let mut idx: usize = 0;

    while idx < extrinsics.len()
        invariant
            idx <= extrinsics.len(),
            first_non_inherent_idx <= idx,
            first_non_inherent_idx <= inherent_count,
            // ... additional loop invariants
    {
        let is_inherent = extrinsics[idx].is_inherent();
        if is_inherent {
            assert(first_non_inherent_idx == idx);
            // From precondition: inherents are contiguous at start
            first_non_inherent_idx = first_non_inherent_idx + 1;
        } else {
            // mode != OnlyInherents (from precondition)
        }
        // apply_extrinsic modeled as external_body
        idx = idx + 1;
    }
}

} // verus!
```

### Phase 4: Model `execute_block` Top-Level (Week 6)

Compose phases 1-3 into a top-level proof:

```rust
verus! {

fn execute_block_model(block: &Block)
    requires
        // === "Correct digests" precondition ===
        block.header.parent_hash == parent_hash_of_chain(),
        block.header.digest == computed_digest_after_full_execution(block),
        block.header.state_root == computed_state_root_after_full_execution(block),
        block.header.extrinsics_root == merkle_root_of(block.extrinsics),
        // === Well-formed block ===
        block.extrinsics_well_encoded(),
        block.inherents_contiguous_at_start(),
        // === Pallet hooks don't panic ===
        pallet_hooks_safe(block),
{
    // 1. Initialize
    let mode = initialize_block_model(&block.header);

    // 2. Initial checks (parent hash)
    initial_checks_model(&block.header);

    // 3. Apply extrinsics
    apply_extrinsics_model(mode, &block.extrinsics, block.inherent_count());

    // 4. Finalize and final checks
    let new_header = finalize_model();
    final_checks_model(&block.header, &new_header);
}

} // verus!
```

### Phase 5: Strengthen and Reduce TCB (Week 7+)

Iteratively:

1. Replace `external_body` pallet hook specs with actual proofs where feasible
   (start with `pallet_timestamp` on_initialize — it's small).
2. Verify SCALE decode round-trip for `DigestItem`.
3. Model the Aura `PreRuntime` digest specifically (slot number decoding).
4. Consider verifying `validate_block` (the parachain-level wrapper) which adds
   additional proof-of-validity checks.

---

## 5. Key Challenges and Mitigations

| Challenge | Severity | Mitigation |
|-----------|----------|------------|
| Verus requires annotated code, not vanilla Rust | High | Model the STF rather than annotate polkadot-sdk in place |
| 40+ pallet hooks are a huge surface area | High | Treat as `external_body` with trusted specs; verify incrementally |
| FRAME macros (`construct_runtime!`, `#[pallet]`) generate complex code | High | Model the generated code's *behavior*, not its syntax |
| Storage host functions are opaque | Medium | Axiomatize with `external_body` + specs (e.g., `get(set(k,v)) == v`) |
| Verus `&mut` support is limited | Medium | Use functional-style models where possible |
| Gap between Verus proof and actual WASM execution | Medium | Accept as TCB; document the assumption clearly |
| SCALE codec correctness | Low | Model `decode(encode(x)) == x` as axiom; optionally verify later |
| Z3 solver timeouts on complex proofs | Medium | Break into small lemmas; use `proof fn` for induction |

---

## 6. Success Criteria

### Minimum Viable Result
- Verus successfully verifies `final_checks_model` given correct-digest preconditions.
- Verus successfully verifies `apply_extrinsics_model` given well-formed-block preconditions.
- All `external_body` trust assumptions are documented.

### Full Result
- Verus verifies `execute_block_model` end-to-end.
- Preconditions ("correct digests" + "well-formed block") are formally stated.
- Trust boundary is minimized and clearly documented.
- At least one pallet hook (`pallet_timestamp::on_initialize`) is verified rather
  than assumed.

### Stretch Goal
- Extend to `validate_block` (cumulus parachain validation wrapper).
- Verify SCALE decode for `DigestItem` and `Header`.
- Integrate with CI to re-check proofs on SDK updates.

---

## 7. References

- **STF entry point**: `polkadot-sdk/substrate/frame/executive/src/lib.rs:695` (`execute_block`)
- **Asset Hub runtime**: `runtimes/system-parachains/asset-hubs/asset-hub-polkadot/src/lib.rs`
- **Digest types**: `polkadot-sdk/substrate/primitives/runtime/src/generic/digest.rs`
- **Header type**: `polkadot-sdk/substrate/primitives/runtime/src/generic/header.rs`
- **Parachain validate_block**: `polkadot-sdk/cumulus/pallets/parachain-system/src/validate_block/implementation.rs`
- **Panic handler**: `polkadot-sdk/substrate/primitives/io/src/lib.rs:1962`
- **Verus repo**: https://github.com/verus-lang/verus
- **Verus guide**: https://verus-lang.github.io/verus/guide/
