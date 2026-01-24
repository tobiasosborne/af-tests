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

---

## Weak Cauchy-Schwarz Implementation (Completed)

**Discovery:** Successfully proved `inner_mul_le_norm_mul_norm_weak` using the
quadratic discriminant approach.

**Key Implementation Details:**

1. **Quadratic expansion helper:** Expand star(a + t•b)*(a + t•b) algebraically
   - Use `star_smul` with `Complex.conj_ofReal` for real t (conj(t) = t)
   - Use `smul_add`, `smul_smul` for distributing scalars
   - Use `abel` (NOT `ring`) for non-commutative additive normalization

2. **Cross-term handling:** Show φ(star a * b + star b * a) = 2 · Re(φ(star b * a))
   - Use `sesqForm_conj_symm` to get φ(star a * b) = conj(φ(star b * a))
   - z + conj(z) = 2 · Re(z)

3. **Discriminant application:**
   - Form quadratic: `(φ(star b * b)).re * t² + 2 * (φ(star b * a)).re * t + (φ(star a * a)).re`
   - Apply `discrim_le_zero` (requires `∀ t, 0 ≤ quadratic(t)`)
   - Use `nlinarith [sq_nonneg ...]` to finish the inequality

4. **Imaginary bound via I·b substitution:**
   - star(I • b) = (-I) • star b (use `Complex.conj_I`)
   - φ(star(I•b) * a) = -I * φ(star b * a), so Re(...) = Im(φ(star b * a))
   - φ(star(I•b) * (I•b)) = φ(star b * b) (since (-I)*I = 1)

**Key Lean Lemmas Used:**
- `discrim_le_zero` from `Mathlib.Algebra.QuadraticDiscriminant`
- `Complex.normSq_apply`: normSq z = z.re² + z.im²
- `Complex.I_mul`: I * z = { re := -z.im, im := z.re }
- `Complex.re_ofNat`, `Complex.im_ofNat`: for simplifying (2 : ℂ).re = 2

**Lesson:** The weak Cauchy-Schwarz (factor 2) is sufficient for many GNS
applications and can be proved with real parameters. The tight bound needs
genuine complex optimization.

---

## Tight Cauchy-Schwarz: Optimal μ Selection (In Progress)

**Discovery:** The tight Cauchy-Schwarz |φ(b*a)|² ≤ φ(a*a)·φ(b*b) requires μ = -c/d
(NOT -conj(c)/d as often stated informally), where c = φ(star b * a), d = φ(star b * b).

**Case Analysis:**
1. **φ(b*b).re = 0:** The weak C-S immediately gives |φ(b*a)|² ≤ 0, so φ(b*a) = 0. ✓ PROVEN
2. **φ(b*b).re > 0:** Complex optimization argument needed. IN PROGRESS

**Key Calculation for Case 2:**
For μ = -c/d where d is real (Im(φ(b*b)) = 0):
```
φ((a + μ•b)*(a + μ•b)) = φ(a*a) + μ*conj(c) + conj(μ)*c + |μ|²*d
                       = φ(a*a) + (-|c|²/d) + (-|c|²/d) + |c|²/d
                       = φ(a*a) - |c|²/d
```
The key insight: μ*conj(c) = -c*conj(c)/d = -|c|²/d is REAL (not just μ*conj(c) + conj(μ)*c).

**Why μ = -c/d works:**
- μ*conj(c) = (-c/d)*conj(c) = -c*conj(c)/d = -|c|²/d (real)
- conj(μ) = -conj(c)/d (since d is real)
- conj(μ)*c = -conj(c)*c/d = -|c|²/d (also real, same value!)
- |μ|² = |c|²/d²
- |μ|²*d = |c|²/d

So the sum is φ(a*a) - 2*|c|²/d + |c|²/d = φ(a*a) - |c|²/d.

**Lean Implementation Challenges:**
1. `star_div'` doesn't exist - need `star_div` or manual computation
2. `field_simp` and `ring` hit recursion limits with complex expressions
3. Need to carefully track real vs complex arithmetic

**Partial Solution:**
- Case 1 proven directly using weak C-S + positivity of normSq
- Case 2 requires more careful algebraic setup, possibly extracting helper lemmas

**Session 2026-01-24 Blockers:**
1. **Term structure:** After `simp [star_add, add_mul, ...]`, smul is nested not flat; `smul_smul` rewrite fails
2. **simp recursion:** Complex division μ = -c/d causes max recursion depth
3. **Rewrite mismatch:** `Complex.mul_re` expands to `μ.re * c.re - μ.im * c.im`, blocking complex-level rewrites

**Proposed fix:** Helper lemmas working in ℝ, avoiding complex division in simp

---

## State Monotonicity via Spectral Ordering (Completed)

**Discovery:** States on C*-algebras preserve the spectral ordering.

**Key Insight:** The spectral order on C*-algebras is defined via `StarOrderedRing`:
```
x ≤ y ↔ ∃ p ∈ AddSubmonoid.closure {star s * s | s}, y = x + p
```
States preserve this because they map `star s * s` to non-negative reals.

**Proof:** Use `AddSubmonoid.closure_induction` - states map star squares to ℝ₊.

**Boundedness:** `star_mul_le_algebraMap_norm_sq` + `star_left_conjugate_le_conjugate`
gives `b*(a*a)*b ≤ ‖a‖² · b*b`, then state monotonicity finishes.

**Setup:** `attribute [local instance] CStarAlgebra.spectralOrder spectralOrderedRing`
