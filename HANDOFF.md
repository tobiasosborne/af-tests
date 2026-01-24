# Handoff: GNS Uniqueness Step 10 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U9 and GNS-U10 (Cyclic vector + Intertwining on quotient)

---

## Completed This Session

1. **Implemented GNS-U9 (af-tests-7em): Prove cyclic vector mapping**
   - `gnsIntertwinerEquiv_cyclic` - Proves `U(Ω_φ) = ξ`

2. **Implemented GNS-U10 (af-tests-2dx): Prove intertwining on quotient**
   - `gnsIntertwiner_intertwines_quotient` - Proves `U(π_φ(a)[b]) = π(a)(U[b])`
   - File: `Main/UniquenessIntertwine.lean` (new, 49 lines)

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (10/12 steps)
- **Build status:** Passing (zero sorries)
- **Files:**
  - `Main/UniquenessExtension.lean` (197 lines)
  - `Main/UniquenessEquiv.lean` (100 lines)
  - `Main/UniquenessIntertwine.lean` (49 lines) - NEW
- **Next ready issue:** `af-tests-5xr` (GNS-U11)

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
| 10 | af-tests-2dx | Intertwining on quotient | Done |
| 11 | af-tests-5xr | Full intertwining | Ready |
| 12 | af-tests-4f9 | Final theorem | Blocked by 11 |

---

## Next Steps

**GNS-U11 (af-tests-5xr):** Full intertwining property
- Extend intertwining from quotient to full Hilbert space by density
- File: `Main/UniquenessIntertwine.lean` (append)

After GNS-U11:
- **GNS-U12:** State final `gns_uniqueness` theorem

---

## Key Implementation Details

### Intertwining on Quotient Proof
```lean
theorem gnsIntertwiner_intertwines_quotient ... :
    gnsIntertwiner ... (φ.gnsPreRep a x : φ.gnsHilbertSpace) =
    π a (gnsIntertwiner ... (x : φ.gnsHilbertSpace)) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective ...
  simp only [gnsPreRep_mk]           -- π_φ(a)[b] = [ab]
  rw [gnsIntertwiner_coe, gnsIntertwiner_coe]  -- reduce to quotient function
  change π (a * b) ξ = π a (π b ξ)   -- both sides explicit
  rw [_root_.map_mul, ContinuousLinearMap.mul_apply]  -- multiplicativity of π
```

The key insight: both sides reduce to `π(ab)ξ` via multiplicativity of the representation.

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessEquiv.lean` (80 → 100 lines)
- Created: `AfTests/GNS/Main/UniquenessIntertwine.lean` (49 lines)
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Quotient-to-Completion Pattern
For properties that hold on the quotient, to extend to the Hilbert space completion:
1. Use `gnsIntertwiner_coe` to reduce to quotient-level function
2. Apply quotient induction to get representatives
3. Use `gnsPreRep_mk` to simplify left multiplication
4. Reduce to algebraic properties (here: multiplicativity of π)

### Multiplicativity of Star Algebra Homomorphisms
`π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` satisfies:
- `_root_.map_mul`: `π(ab) = π(a) * π(b)` (as multiplication in the target ring)
- `ContinuousLinearMap.mul_apply`: `(f * g) x = f (g x)` (composition)
