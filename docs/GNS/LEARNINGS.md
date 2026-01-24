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

## 2026-01-24: Cauchy-Schwarz Proof Strategy

**Discovery:** The standard quadratic discriminant argument for Cauchy-Schwarz
requires careful handling of real vs complex parameters.

**Problem:** The `discrim_le_zero` lemma works for polynomials over ordered fields
(like ℝ), but the Cauchy-Schwarz for sesquilinear forms needs |φ(b*a)|² ≤ φ(a*a)·φ(b*b).
Using real t : ℝ gives bounds on Re² and Im² separately, which sum to 2× the bound.

**Mathematical Detail:**
- For t : ℝ, expand φ((a + t·b)*(a + t·b)) ≥ 0 as a quadratic in t
- Apply discrim_le_zero to get Re(φ(b*a))² ≤ φ(a*a)·φ(b*b)
- Repeat with i·b to get Im(φ(b*a))² ≤ φ(a*a)·φ(b*b)
- But Re² + Im² ≤ 2·bound (not tight!)

**Resolution for tight bound:**
- Use complex λ ∈ ℂ instead of real t
- Set λ = -conj(φ(b*a))/φ(b*b) when φ(b*b) ≠ 0
- This eliminates the cross-term and gives the tight bound
- Case φ(b*b) = 0 handled separately (implies φ(b*a) = 0)

**Lesson:** When adapting real-variable proofs to complex settings, the tight
constant often requires genuinely complex parameters, not just "apply twice."

**Lean-specific note:** The tactic `ring` doesn't work on non-commutative rings.
Use manual rewrites with `smul_mul_assoc`, `mul_smul_comm`, `smul_smul` for
expansions involving scalar multiplication in C*-algebras.

---

## 2026-01-24: Project Audit - Documentation Drift Detection

**Discovery:** A systematic audit of the GNS subproject revealed 8 instances of
drift between documentation and implementation.

**Key Findings:**

1. **Naming mismatch** - `01_states.md` documents `State.cauchy_schwarz` but actual
   theorem is `State.inner_mul_le_norm_mul_norm`

2. **Misplaced theorem** - `null_space_left_ideal` is in CauchySchwarz.lean but:
   - Proof requires "boundedness", not Cauchy-Schwarz
   - Separate beads issue exists for NullSpace/LeftIdeal.lean
   - Creates unclear responsibility boundaries

3. **Status terminology** - "DONE" vs "Ready" undefined. Phase 1 marked "DONE"
   but has 4 sorries. Is "DONE" = structure complete, or fully proven?

4. **LOC target drift** - CauchySchwarz planned 50-70 LOC, actual 95 LOC

5. **Stale line numbers** - HANDOFF.md line numbers off by 1

**Resolution:** Created 9 beads issues to track all findings:
- P0: af-tests-7kl (naming)
- P1: af-tests-op0 (misplaced theorem), af-tests-aea (status semantics)
- P2: af-tests-9u6 (LOC target), af-tests-pzj (line numbers)
- P3: af-tests-uo6, af-tests-03g, af-tests-bgs, af-tests-wmn (sorry elimination)

**Lesson:** Regular audits catch drift before it compounds. Documentation that
isn't systematically verified against implementation will diverge. Consider
automated checks (e.g., grep for documented names in code).

---

## 2026-01-24: Left Ideal Property DOES Use Cauchy-Schwarz (Corrected)

**Discovery:** The left ideal property (ba ∈ N_φ when a ∈ N_φ) CAN be proven
using Cauchy-Schwarz, contrary to the earlier incorrect claim about boundedness.

**Proof (implemented in NullSpace/LeftIdeal.lean):**
1. Need: φ((ba)*(ba)) = 0 when φ(a*a) = 0
2. Compute: (ba)*(ba) = a* b* b a = a* · (b*ba)
3. By Cauchy-Schwarz (swapped): |φ(a* · x)|² ≤ φ(x*x).re · φ(a*a).re
4. Since φ(a*a) = 0, we get φ(a* · x) = 0 for all x
5. Taking x = b*ba gives φ((ba)*(ba)) = 0

**Key insight:** The "swapped" Cauchy-Schwarz lemma:
- Original: `apply_star_mul_eq_zero_of_apply_star_self_eq_zero` gives φ(x*a) = 0
- Swapped: `apply_mul_star_eq_zero_of_apply_star_self_eq_zero` gives φ(a*x) = 0
Both follow from the same `inner_mul_le_norm_mul_norm` theorem.

**Lesson:** When a proof seems to require a stronger hypothesis (like boundedness),
try rearranging the existing lemmas. The "swapped" version of a consequence may
be exactly what you need.

---

## 2026-01-24: Quotient Module Construction in Mathlib

**Discovery:** Constructing the quotient A ⧸ N_φ requires upgrading from `AddSubgroup`
to `Submodule ℂ A`.

**Key Mathlib APIs:**
- `Submodule.mkQ` : the quotient map `A →ₗ[ℂ] A ⧸ N`
- `Submodule.liftQ` : lift a linear map through the quotient (requires `N ≤ ker f`)
- `Submodule.Quotient.mk` : the element-level quotient constructor
- `Submodule.Quotient.mk_add` : `mk (a + b) = mk a + mk b`
- `Submodule.Quotient.mk_surjective` : every element has a representative

**Extensionality Pattern:** When proving `f = g` for linear maps on quotients:
```lean
ext x  -- gives x : A (the underlying type)
-- Goal becomes: (f ∘ₗ mkQ) x = (g ∘ₗ mkQ) x
simp [mkQ_apply, ...]
```

**Lesson:** The `ext` tactic for quotient modules doesn't give you `x : A ⧸ N`;
it gives you `x : A` and a goal involving `mkQ x`. Structure your proofs accordingly.

---

## Template for New Entries

```markdown
## YYYY-MM-DD: Brief Title

**Discovery:** What you found

**Problem:** Why it matters

**Resolution:** How you fixed/addressed it

**Lesson:** General takeaway for future work
```
