# State and Positivity Learnings

Technical discoveries related to state definitions and positivity in C*-algebras.

---

## State Definition Requires Im = 0

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

## Conjugate Symmetry via Algebraic Polarization

**Discovery:** The proof of `sesqForm_conj_symm` (φ(star y * x) = conj(φ(star x * y)))
uses a clever algebraic trick rather than explicit polarization formulas.

**Proof Strategy:**
Let P = φ(star y * x) and Q = φ(star x * y). We want P = conj(Q).

1. **Sum is real:** D = star y * x + star x * y = star(x+y)*(x+y) - star x * x - star y * y
   - All terms on RHS map to ℝ (diagonal elements), so (P + Q).im = 0
   - Thus P.im = -Q.im

2. **i × difference is real:** I•(Q - P) = star(x+I•y)*(x+I•y) - star x * x - star y * y
   - All terms on RHS map to ℝ, so (I*(Q - P)).im = 0
   - Since (I*z).im = z.re, we get (Q - P).re = 0
   - Thus P.re = Q.re

3. **Combine:** P.re = Q.re and P.im = -Q.im means P = conj(Q) ✓

**Key Lean Tactics:**
- `star_smul`: star(c • a) = conj(c) • star(a)
- `smul_mul_assoc`, `mul_smul_comm`: handle scalar positioning in products
- `abel` for additive groupoid normalization (instead of `ring` for non-commutative)
- `Complex.I_mul`: I * z = { re := -z.im, im := z.re }

**Lesson:** When proving properties of sesquilinear forms over C*-algebras, express
cross-terms as differences of diagonal elements. The state's reality condition
φ(star z * z) ∈ ℝ then provides strong algebraic constraints.

---

## ℂ Has No Natural PartialOrder in Mathlib

**Discovery:** Cannot directly use `PositiveLinearMap` for states to ℂ because
mathlib's `PositiveLinearMap` requires `PartialOrder` and `StarOrderedRing` on
the codomain, which ℂ doesn't have.

**Workaround:** Define State using `ContinuousLinearMap` with explicit positivity
conditions rather than inheriting from PositiveLinearMap.

**Lesson:** Check typeclass requirements carefully before choosing a base type.

---

## Cauchy-Schwarz Proof Strategy

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
