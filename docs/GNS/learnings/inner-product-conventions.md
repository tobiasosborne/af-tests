# Inner Product Convention Learnings

Technical discoveries related to inner product conventions and instance construction.

---

## Inner Product Convention Mismatch (Physics vs Math)

**Discovery:** The GNS inner product `⟨[a], [b]⟩ = φ(b*a)` is linear in the first
argument (physics convention), but mathlib's `PreInnerProductSpace.Core` expects
conjugate-linearity in the first argument (math convention).

**Problem:** Our `gnsInner_smul_left` proves `⟨c·x, y⟩ = c · ⟨x, y⟩`, but mathlib
needs `⟨c·x, y⟩ = conj(c) · ⟨x, y⟩`. These are incompatible!

**Mathematical Detail:**
- GNS definition: `⟨[a], [b]⟩ = φ(b*a)` makes ⟨·,·⟩ linear in first arg
- Math convention: `⟨·,·⟩` is conjugate-linear in first, linear in second
- Physics convention: `⟨·,·⟩` is linear in first, conjugate-linear in second

**Resolution:** Define the mathlib `Inner` instance with swapped arguments:
```lean
instance gnsQuotientInner : Inner ℂ φ.gnsQuotient :=
  ⟨fun x y => φ.gnsInner y x⟩  -- Note: y x, not x y
```
This makes `inner x y = gnsInner y x`, which is conjugate-linear in first arg.

**Key lemma needed:** `gnsInner_smul_right`:
```lean
φ.gnsInner x (c • y) = starRingEnd ℂ c * φ.gnsInner x y
```
Derived from `gnsInner_smul_left` + `gnsInner_conj_symm`.

**Lesson:** Always check which convention mathlib uses before building instances.
The physics convention is common in quantum mechanics but mathlib uses math.

---

## Building InnerProductSpace from Core (Instance Chain)

**Discovery:** `InnerProductSpace.ofCore` requires `SeminormedAddCommGroup` first.

**Problem:** Creating instances in wrong order causes diamond issues where mathlib
expects one `SeminormedAddCommGroup` but finds another.

**Resolution:** Use explicit `@` syntax to build the chain consistently:
```lean
noncomputable instance gnsQuotientSeminormedAddCommGroup :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ φ.gnsPreInnerProductCore

noncomputable instance gnsQuotientNormedSpace :=
  @InnerProductSpace.Core.toNormedSpace ℂ _ _ _ _ φ.gnsPreInnerProductCore
```
Then build `InnerProductSpace` using the same Core.

**Lesson:** When building typeclass instances from Core structures, use explicit
`@` application to ensure all instances derive from the same source.

---

## State Spectral Ordering and Boundedness

**Discovery:** Proving `‖π(a)x‖ ≤ ‖a‖ * ‖x‖` requires showing states respect the
C*-algebra spectral ordering.

**Problem:** The proof needs:
1. `CStarAlgebra.star_mul_le_algebraMap_norm_sq`: `a*a ≤ ‖a‖² · 1`
2. `conjugate_le_conjugate`: `b*(a*a)b ≤ b*(‖a‖² · 1)b = ‖a‖² · b*b`
3. States preserve ordering: if `x ≤ y` then `(φ x).re ≤ (φ y).re`

The third step is non-trivial because:
- States map to ℂ, which lacks `StarOrderedRing`
- We know `φ(a*a) ≥ 0` is real, but not for all positive cone elements
- The spectral order uses closure of `{s*s}`, not just star_mul_self

**Resolution:** Left as sorry (af-tests-z9g). Possible approaches:
- Prove states are positive on the full spectral cone
- Use continuous functional calculus directly
- Find an alternative proof avoiding spectral order

**Lesson:** Mathlib's spectral order infrastructure is powerful but states to ℂ
don't fit the `OrderHomClass` pattern directly. Need custom positivity lemmas.

---

## Proving Star Property via Adjoint Characterization

**Discovery:** To prove `π(a*) = π(a).adjoint`, use `ContinuousLinearMap.eq_adjoint_iff`.

**Problem:** Need to show `⟪π(a*)x, y⟫ = ⟪x, π(a)y⟫` for all x, y in the Hilbert
space completion. The inner product on completions is defined via density.

**Resolution:**
1. Use `ContinuousLinearMap.eq_adjoint_iff`: `A = B† ↔ ∀ x y, ⟪Ax, y⟫ = ⟪x, By⟫`
2. Apply `UniformSpace.Completion.induction_on₂` to reduce to dense quotient elements
3. Use `UniformSpace.Completion.inner_coe` to compute inner products on embedded elements
4. **Crucial:** Account for the argument swap from `inner_eq_gnsInner_swap`:
   - mathlib's `⟪x, y⟫ = gnsInner y x` (arguments swapped!)
   - So `⟪π(a*)[b], [c]⟫ = gnsInner [c] [a*b]`, not `gnsInner [a*b] [c]`

**Key Lemma Pattern:**
```lean
theorem gnsPreRep_inner_star (a b c : A) :
    φ.gnsInner (Submodule.Quotient.mk c) (φ.gnsPreRep (star a) (Submodule.Quotient.mk b)) =
    φ.gnsInner (φ.gnsPreRep a (Submodule.Quotient.mk c)) (Submodule.Quotient.mk b) := by
  simp only [gnsPreRep_mk, gnsInner_mk, star_mul, star_star, mul_assoc]
```

**Lesson:** When working with the mathlib inner product on completions, always track
which convention is used. The `inner_eq_gnsInner_swap` lemma is essential for
converting between the two conventions.

---

## GNS Uniqueness Intertwiner: Quotient Lift via Well-Definedness

**Discovery:** The GNS uniqueness intertwiner U₀ : A/N_φ → H is constructed via
`Quotient.liftOn`, which requires proving well-definedness on equivalence classes.

**Key Insight:** If [a] = [b] in A/N_φ (i.e., a - b ∈ N_φ), then π(a)ξ = π(b)ξ.

**Proof Technique:**
1. From a - b ∈ N_φ, we have φ((a-b)*(a-b)) = 0
2. Use `inner_self_eq_zero ℂ`: π(a-b)ξ = 0 ↔ ⟨π(a-b)ξ, π(a-b)ξ⟩ = 0
3. Apply `ContinuousLinearMap.adjoint_inner_right`: ⟨π(a-b)ξ, π(a-b)ξ⟩ = ⟨ξ, π(a-b)† π(a-b)ξ⟩
4. Use *-representation property: π(a-b)† = π((a-b)*)
5. Use multiplication property: π((a-b)*) π(a-b) = π((a-b)*(a-b))
6. Apply state condition: ⟨ξ, π((a-b)*(a-b))ξ⟩ = φ((a-b)*(a-b)) = 0

**Implementation Note:** The `change` tactic is essential when working with
`Quotient.liftOn` on `Submodule.Quotient.mk`, as the definitional equality isn't
always recognized by `simp`. Use `change` to make the goal match the expected form.

**Lesson:** Proving well-definedness of quotient maps often reduces to showing
the null space condition implies the desired equality. The adjoint inner product
identity is the key tool for connecting inner products to the state.
