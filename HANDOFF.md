# Handoff: GNS Uniqueness COMPLETE

**Date:** 2026-01-24
**Session Focus:** Complete GNS uniqueness theorem (Steps 9-12)

---

## Completed This Session

1. **GNS-U9 (af-tests-7em): Cyclic vector mapping**
   - `gnsIntertwinerEquiv_cyclic` - Proves `U(Ω_φ) = ξ`

2. **GNS-U10 (af-tests-2dx): Intertwining on quotient**
   - `gnsIntertwiner_intertwines_quotient` - Proves `U(π_φ(a)[b]) = π(a)(U[b])`

3. **GNS-U11 (af-tests-5xr): Full intertwining**
   - `gnsIntertwiner_intertwines` - Proves `U(π_φ(a)x) = π(a)(Ux)` for all x

4. **GNS-U12 (af-tests-4f9): FINAL UNIQUENESS THEOREM**
   - `gns_uniqueness` - The complete GNS uniqueness theorem

---

## Final State

- **GNS existence theorem (`gns_theorem`):** PROVEN
- **GNS uniqueness theorem (`gns_uniqueness`):** PROVEN
- **Build status:** Passing (zero sorries)
- **All 12 uniqueness steps:** COMPLETE

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1-8 | various | Foundation steps | Done |
| 9 | af-tests-7em | Cyclic vector mapping | Done |
| 10 | af-tests-2dx | Intertwining on quotient | Done |
| 11 | af-tests-5xr | Full intertwining | Done |
| 12 | af-tests-4f9 | Final theorem | Done |

**ALL STEPS COMPLETE**

---

## Uniqueness Files Created

| File | Lines | Purpose |
|------|-------|---------|
| `Main/Uniqueness.lean` | 189 | Quotient-level intertwiner |
| `Main/UniquenessExtension.lean` | 197 | Extension to Hilbert space |
| `Main/UniquenessEquiv.lean` | 100 | LinearIsometryEquiv + cyclic vector |
| `Main/UniquenessIntertwine.lean` | 79 | Intertwining property |
| `Main/UniquenessTheorem.lean` | 57 | Final theorem statement |
| **Total** | **622** | |

---

## The GNS Uniqueness Theorem

```lean
theorem gns_uniqueness
    (_hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    ∃ U : φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H,
      U φ.gnsCyclicVector = ξ ∧
      ∀ a : A, ∀ x : φ.gnsHilbertSpace, U (φ.gnsRep a x) = π a (U x)
```

**Translation:** For any cyclic *-representation (H, π, ξ) implementing the state φ,
there exists a unitary equivalence U from the GNS Hilbert space to H that:
1. Maps the canonical cyclic vector Ω_φ to ξ
2. Intertwines the representations: U ∘ π_φ(a) = π(a) ∘ U

---

## Key Learnings This Session

### Completion Induction Pattern
```lean
induction x using UniformSpace.Completion.induction_on with
| hp => apply isClosed_eq <cont_lhs> <cont_rhs>
| ih y => <reduce to quotient case>
```

### Clean Proof Chains
The cyclic vector mapping proof chains through abstraction layers:
- `gnsIntertwinerEquiv_apply` → `gnsCyclicVector_eq_coe` → `gnsIntertwiner_coe` → `gnsIntertwinerQuotient_cyclic`

### Multiplicativity of Star Algebra Homomorphisms
- `_root_.map_mul`: `π(ab) = π(a) * π(b)`
- `ContinuousLinearMap.mul_apply`: `(f * g) x = f (g x)`

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessEquiv.lean` (80 → 100 lines)
- Created: `AfTests/GNS/Main/UniquenessIntertwine.lean` (79 lines)
- Created: `AfTests/GNS/Main/UniquenessTheorem.lean` (57 lines)
- Modified: `HANDOFF.md` (this file)
