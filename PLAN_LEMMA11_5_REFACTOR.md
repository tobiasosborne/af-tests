# Plan: Refactoring Lemma 11.5 for n, k, m ≥ 3

## Current Status
- **File:** `AfTests/Primitivity/Lemma11_5_Case2.lean`
- **Issue:** Contains a `sorry` at line 796 inside the `n=3` branch of `case2_impossible`.
- **Context:** The current proof attempts a brittle brute-force calculation of `g₁` indices for `n=3` and `n>3`. This has led to ~1000 lines of complex, hard-to-maintain arithmetic code that is currently broken.
- **Goal:** Prove `case2_impossible` for all `n ≥ 1` by replacing the brittle arithmetic with a robust structural argument derived from the block system properties.

## Proposed Strategy: Structural Block Argument

Instead of calculating specific array indices for `g₁^n`, we will use the global properties of the block system.

### 1. Mathematical Argument (for n ≥ 3)

**Assumptions:**
- `B` is a block in a valid block system `BS`.
- `g₁(B) ≠ B` (Case 2 assumption).
- We have already proven `B ⊆ tailA` and `g₂(B) = B`.
- `tailA ⊆ supp(g₁)`.

**The Proof:**
1.  **Orbit Partition:** The orbit of `B` under `g₁`, denoted `{g₁^j(B)}`, forms a partition of `supp(g₁)`.
    *   *Reason:* `g₁` acts transitively on `supp(g₁)`. Since `B ⊆ supp(g₁)`, its orbit covers `supp(g₁)`.
2.  **Target Block:** There exists a block `B'` in this orbit such that `1 ∈ B'`.
    *   *Reason:* `1 ∈ supp(g₁)` (for `n ≥ 1`), so it must be in one of the partition blocks.
3.  **Containment:** `B' ⊆ supp(g₁)`.
    *   *Reason:* `B ⊆ supp(g₁)` and `supp(g₁)` is invariant under `g₁`.
4.  **Action of g₂:**
    *   `g₂` preserves the block system (global H-invariance).
    *   `g₂(1) = 2`.
5.  **Disjointness Contradiction:**
    *   **Not Invariant:** `g₂(B') ≠ B'`.
        *   *Proof:* `1 ∈ B'`, so `g₂(1) = 2 ∈ g₂(B')`. But `2 ∉ supp(g₁)` (for `n ≥ 1`), so `2 ∉ B'`. Thus `g₂(B')` contains an element not in `B'`.
    *   **Not Disjoint:** `g₂(B') ∩ B' ≠ ∅`.
        *   *Proof:*
            *   `B'` contains at least 2 elements (since `|B'| = |B| > 1`).
            *   `B' ⊆ supp(g₁)`.
            *   The intersection `supp(g₁) ∩ supp(g₂)` is exactly `{1, 4}`.
            *   `g₂` fixes all elements in `supp(g₁)` *except* 1 and 4.
            *   If `B'` contained *only* 1 and 4, then `|B'|=2`. This implies the block system has blocks of size 2. Since `supp(g₁)` has size `n+4`, `n+4` must be even.
            *   However, for `n ≥ 3`, we can show `B'` must contain a "tail" element `y ∈ tailA` (or similar structural element) that is fixed by `g₂`.
            *   Let `y ∈ B'` be such a fixed point (`g₂(y) = y`).
            *   Then `y ∈ B'` and `y = g₂(y) ∈ g₂(B')`.
            *   So `B' ∩ g₂(B') ≠ ∅`.
    *   **Conclusion:** `g₂` neither fixes `B'` nor moves it disjointly. This contradicts the definition of a block system.

### 2. Implementation Plan

#### Step A: Refactor `case2_impossible` Signature
Update `AfTests/Primitivity/Lemma11_5_Case2.lean`.

**Current Signature:**
```lean
theorem case2_impossible (hn : n ≥ 1) (B : Set (Omega n k m)) ...
    (hBlock : ∀ j : ℕ, (g₁ n k m ^ j) '' B = B ∨ Disjoint ((g₁ n k m ^ j) '' B) B) ...
```

**New Signature:**
```lean
theorem case2_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₁Disj : Disjoint (g₁ n k m '' B) B)
    (ha₁_in_B : a₁ n k m hn ∈ B)
    ...
```
*Note: We replace the local `hBlock` hypothesis with the full `BS` context to access the partition property.*

#### Step B: Implement the Logic
Inside `case2_impossible`:
1.  Keep the `n=1` and `n=2` cases (they are proven and working).
2.  For `n ≥ 3`:
    *   Use `BS.isPartition` to obtain `B'` such that `1 ∈ B'`.
    *   Prove `B' ∈ BS.blocks`.
    *   Prove `B' ⊆ supp(g₁)` (using `B ⊆ tailA`).
    *   Prove `g₂(B') ≠ B'` via `1 → 2`.
    *   Prove `¬Disjoint g₂(B') B'` via existence of fixed point `y ∈ B'`.

#### Step C: Update Symmetric Cases
Apply the same logic to:
*   `AfTests/Primitivity/Lemma11_5_SymmetricCases.lean`: `case2_impossible_B` (for `k ≥ 3`).
*   `AfTests/Primitivity/Lemma11_5_SymmetricCases.lean`: `case2_impossible_C` (for `m ≥ 3`).

#### Step D: Update Call Sites
*   `AfTests/Primitivity/Lemma11_5.lean`: Update `lemma11_5_no_nontrivial_blocks` to pass the `BS` object to the refactored lemmas.

## Impact Analysis
*   **Safety:** High. We are replacing broken/incomplete code with a logically sound argument backed by the Natural Language proof.
*   **Diff Size:** Large deletion of brittle code (~1000 lines), small insertion of structural code (~100 lines). Net reduction in code size.
*   **Verification:** This aligns exactly with the "Fixed Point Argument" described in `examples/lemmas/lemma11_5_no_nontrivial_blocks.md` (Nodes 1.9.3, 1.9.5).

## Next Steps
1.  Wait for user approval of this plan.
2.  Execute Step A & B (Refactor `Lemma11_5_Case2.lean`).
3.  Execute Step C (Refactor `Lemma11_5_SymmetricCases.lean`).
4.  Execute Step D (Update `Lemma11_5.lean`).
5.  Verify build passes.
