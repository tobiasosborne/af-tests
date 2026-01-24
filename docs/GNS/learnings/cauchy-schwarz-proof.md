# Cauchy-Schwarz Proof Learnings

Technical discoveries from proving the Cauchy-Schwarz inequality for states.

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

## Weak Cauchy-Schwarz Implementation

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
applications and can be proved with real parameters.

---

## Tight Cauchy-Schwarz: Optimal μ Selection

**Discovery:** The tight Cauchy-Schwarz |φ(b*a)|² ≤ φ(a*a)·φ(b*b) requires μ = -c/d
(NOT -conj(c)/d as often stated informally), where c = φ(star b * a), d = φ(star b * b).

**Case Analysis:**
1. **φ(b*b).re = 0:** The weak C-S immediately gives |φ(b*a)|² ≤ 0, so φ(b*a) = 0.
2. **φ(b*b).re > 0:** Complex optimization argument needed.

**Key Calculation for Case 2:**
For μ = -c/d where d is real (Im(φ(b*b)) = 0):
```
φ((a + μ•b)*(a + μ•b)) = φ(a*a) + μ*conj(c) + conj(μ)*c + |μ|²*d
                       = φ(a*a) + (-|c|²/d) + (-|c|²/d) + |c|²/d
                       = φ(a*a) - |c|²/d
```

**Why μ = -c/d works:**
- μ*conj(c) = (-c/d)*conj(c) = -c*conj(c)/d = -|c|²/d (real)
- conj(μ) = -conj(c)/d (since d is real)
- conj(μ)*c = -conj(c)*c/d = -|c|²/d (also real, same value!)
- |μ|² = |c|²/d²
- |μ|²*d = |c|²/d

So the sum is φ(a*a) - 2*|c|²/d + |c|²/d = φ(a*a) - |c|²/d.

---

## Tight Cauchy-Schwarz: Lean Implementation

**Challenges Encountered:**
1. `star_div'` doesn't exist - need `star_div` or manual computation
2. `field_simp` and `ring` hit recursion limits with complex expressions
3. Need to carefully track real vs complex arithmetic

**Session Blockers (2026-01-24):**
1. After `simp [star_add, add_mul, ...]`, smul is nested not flat; `smul_smul` rewrite fails
2. Complex division μ = -c/d causes max recursion depth in simp
3. `Complex.mul_re` expands to `μ.re * c.re - μ.im * c.im`, blocking complex-level rewrites

**Resolution:** Eliminated the sorry by avoiding simp entirely:

1. **Let binding unfold:** The `let μ := -c/d` binding causes syntactic mismatch
   with `rw`. Use `simp only [show μ = -c / d from rfl]` to unfold it first.

2. **Addition reassociation:** Use `convert ... using 2; ring` to restructure
   terms before pattern matching.

3. **Complex division real-part extraction:** `((-a : ℂ) / b).re` requires explicit
   `Complex.div_ofReal_re`, `Complex.neg_re`, `Complex.ofReal_re` rewrites.

4. **Final inequality step:** Multiply by `d.re > 0`, expand with `add_mul`, then
   use `div_mul_cancel₀` to simplify `(-|c|²/d.re) * d.re = -|c|²`.

**Final proof structure:**
- `cross_term_opt_identity`: algebraic identity without `let` binding
- Main proof: unfold μ → reassociate → apply identity → extract real part → linarith

**Key Lemmas:**
- `Complex.div_ofReal_re`: (z / r).re = z.re / r for real r
- `Complex.mul_conj`: z * conj(z) = normSq(z)
- `div_mul_cancel₀`: (a / b) * b = a when b ≠ 0
