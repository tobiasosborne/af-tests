# GNS Construction: Technical Learnings

This file documents technical discoveries, gotchas, and insights gained during
implementation. **Errors are not failures** - they teach us what works and what
doesn't.

---

## 2026-01-24: State Definition Requires Im = 0

**Discovery:** The original State definition using only `Re(φ(a*a)) ≥ 0` was
insufficient to prove `map_star`.

**Problem:** To prove `φ(a*) = conj(φ(a))`, the polarization identity requires
that `φ(z*z)` is REAL (not just has non-negative real part). Without this, the
proof of conjugate symmetry fails.

**Mathematical Detail:**
- Polarization: `4φ(y*x) = R₁ - R₂ + i(R₃ - R₄)` where Rᵢ = φ(zᵢ*zᵢ)
- If Rᵢ are only "Re ≥ 0", the imaginary part (R₃ - R₄) is unconstrained
- If Rᵢ ∈ ℝ, then R₃ = R₄ (both equal φ(D) where D is self-adjoint part)

**Resolution:** Added `map_star_mul_self_real : Im(φ(a*a)) = 0` to State structure.

**Lesson:** When formalizing, the mathematical literature's "obviously positive"
often hides "real AND non-negative". Be explicit about both conditions.

---

## 2026-01-24: ℂ Has No Natural PartialOrder in Mathlib

**Discovery:** Cannot directly use `PositiveLinearMap` for states to ℂ because
mathlib's `PositiveLinearMap` requires `PartialOrder` and `StarOrderedRing` on
the codomain, which ℂ doesn't have.

**Workaround:** Define State using `ContinuousLinearMap` with explicit positivity
conditions rather than inheriting from PositiveLinearMap.

**Lesson:** Check typeclass requirements carefully before choosing a base type.

---

## Template for New Entries

```markdown
## YYYY-MM-DD: Brief Title

**Discovery:** What you found

**Problem:** Why it matters

**Resolution:** How you fixed/addressed it

**Lesson:** General takeaway for future work
```
