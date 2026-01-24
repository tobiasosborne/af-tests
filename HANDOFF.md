# Handoff: GNS Uniqueness Step 9 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U9 (Cyclic vector mapping)

---

## Completed This Session

1. **Implemented GNS-U9 (af-tests-7em): Prove cyclic vector mapping**
   - `gnsIntertwinerEquiv_cyclic` - Proves `U(Ω_φ) = ξ`
   - Proof chain: `gnsIntertwinerEquiv_apply` → `gnsCyclicVector_eq_coe` → `gnsIntertwiner_coe` → `gnsIntertwinerQuotient_cyclic`

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (9/12 steps)
- **Build status:** Passing (zero sorries)
- **Files:**
  - `Main/UniquenessExtension.lean` (197 lines)
  - `Main/UniquenessEquiv.lean` (100 lines)
- **Next ready issue:** `af-tests-2dx` (GNS-U10)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | Done |
| 2 | af-tests-6tj | LinearMap structure | Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Done |
| 4 | af-tests-hqt | Extension to Hilbert space | Done |
| 5 | af-tests-ywt | Extension is isometry | Done |
| 6 | af-tests-5nd | Dense range | Done |
| 7 | af-tests-usd | Surjectivity | Done |
| 8 | af-tests-7hr | LinearIsometryEquiv | Done |
| 9 | af-tests-7em | Cyclic vector mapping | Done |
| 10 | af-tests-2dx | Intertwining on quotient | Ready |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 11 |

---

## Next Steps

**GNS-U10 (af-tests-2dx):** Intertwining on quotient
- Prove `U([ab]) = π(a)(U[b])` on quotient elements
- File: `Main/UniquenessIntertwine.lean` (new)

After GNS-U10 unblocks:
- **GNS-U11:** Extend intertwining to full Hilbert space by density
- **GNS-U12:** State final `gns_uniqueness` theorem

---

## Key Implementation Details

### Cyclic Vector Mapping Proof
```lean
theorem gnsIntertwinerEquiv_cyclic ... : gnsIntertwinerEquiv ... φ.gnsCyclicVector = ξ := by
  rw [gnsIntertwinerEquiv_apply]   -- U = gnsIntertwiner
  rw [gnsCyclicVector_eq_coe]      -- Ω_φ = embed([1])
  rw [gnsIntertwiner_coe]          -- U(embed(x)) = U₀(x)
  exact gnsIntertwinerQuotient_cyclic ...  -- U₀([1]) = ξ
```

The proof elegantly chains: equiv → CLinMap → extension_coe → quotient property.

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessEquiv.lean` (80 → 100 lines)
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Clean Proof Chains via Rewriting
The cyclic vector mapping proof is a textbook example of using `rw` to chain through
multiple levels of abstraction:
1. `LinearIsometryEquiv` → `ContinuousLinearMap` (by definition)
2. Hilbert space element → embedded quotient element
3. Extension on embedded → original function on quotient
4. Quotient function on `[1]` → `ξ`

Each step is definitional or uses a previously proven lemma. No computation needed.
