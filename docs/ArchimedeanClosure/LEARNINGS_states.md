# States and Bounds Learnings

## MPositiveState Definition

### Structure
```lean
structure MPositiveState (n : ℕ) where
  toFun : FreeStarAlgebra n →ₗ[ℝ] ℝ
  map_star : ∀ a, toFun (star a) = toFun a
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ toFun m
  map_one : toFun 1 = 1
```

### Design Decisions

1. **Codomain is ℝ, not ℂ**: No need for `map_m_real` - automatic.

2. **Explicit `map_star` condition**: The symmetry `φ(star a) = φ(a)` is part of structure
   - Mathematically cleaner
   - Easier to work with (available immediately)
   - Matches physics literature

3. **No `selfAdjoint` subtype**: Would require proving `StarModule ℝ` for FreeAlgebra.

---

## NonEmptiness Proof (Scalar Extraction)

### Key Insight
`scalarExtraction` is an **algebra homomorphism**:
```lean
scalarExtraction(star a * a) = scalarExtraction(star a) * scalarExtraction(a)
                              = scalarExtraction(a)²
```
And `x² ≥ 0` for all `x : ℝ`.

### Theorems Proven
1. `scalarExtraction_star`: φ(star a) = φ(a)
2. `scalarExtraction_star_mul_self_nonneg`: φ(star a * a) ≥ 0
3. `scalarExtraction_star_mul_generator_mul_self_nonneg`: φ(star a * g_j * a) = 0
4. `scalarExtraction_m_nonneg`: φ(m) ≥ 0 for all m ∈ M
5. `scalarState`: Constructs the canonical M-positive state
6. `MPositiveStateSet_nonempty`: S_M ≠ ∅

### Generator-Weighted Squares
For `star a * g_j * a`, scalar extraction gives 0 (not just ≥ 0):
- `scalarExtraction` is an algebra hom
- `scalarExtraction(g_j) = 0` for generators
- So the whole product is 0

---

## Cauchy-Schwarz for M-Positive States (AC-P3.1)

### Result
`φ(star b * a)² ≤ φ(star a * a) · φ(star b * b)`

### Key Lemmas
1. `star_smul_real`: `star(c • a) = c • star a` for `c : ℝ`
2. `sesqForm_symm`: `φ(star a * b) = φ(star b * a)`
3. `quadratic_nonneg`: Discriminant setup
4. `cauchy_schwarz`: Main theorem via discriminant
5. `apply_sq_le`: Corollary `φ(a)² ≤ φ(star a * a)`

### Technical Note: star_smul
FreeAlgebra lacks `StarModule`, so prove manually:
```lean
star (c • a) = star (algebraMap c * a)     -- Algebra.smul_def
            = star a * star (algebraMap c) -- star_mul
            = star a * algebraMap c        -- FreeAlgebra.star_algebraMap
            = algebraMap c * star a        -- Algebra.commutes
            = c • star a                   -- Algebra.smul_def
```

---

## Archimedean Bound (AC-P3.2)

### Results
- `φ(star a * a) ≤ Nₐ`
- `φ(a)² ≤ Nₐ`
- `|φ(a)| ≤ √Nₐ`

### Proof Strategy
1. Archimedean property: `N·1 - star a * a ∈ M`
2. M-positivity: `φ(N·1 - star a * a) ≥ 0`
3. Linearity: `N·φ(1) - φ(star a * a) ≥ 0`
4. Normalization: `N - φ(star a * a) ≥ 0` (since `φ(1) = 1`)

### FunLike Coercion Issue
When working with `MPositiveState` (which has `FunLike` instance):
- `map_neg φ.toFun` works
- `map_neg φ` does NOT (different coercion)

**Solution**: Use `congr 1` + `exact φ.toFun.map_neg _` instead of simp.

---

## Generating Cone Lemma (AC-P3.3)

### Main Result
Every self-adjoint element is a difference of M-elements:
`x = ¼(1+x)² - ¼(1-x)² ∈ M - M`

### Why This Matters
Shows that M "generates" the self-adjoint cone, needed for Riesz extension.

### Key Theorems
- `selfAdjoint_decomp`: The algebraic identity
- `decomp_terms_in_M`: Both terms are in M
- `quadraticModule_selfAdjoint_generating`: Final result

See [LEARNINGS_proofs.md](LEARNINGS_proofs.md) for the selfAdjoint_decomp proof.

---

## Classical.choose vs Nat.find

### Challenge
`Nat.find` requires `DecidablePred`, but M membership is not decidable.

### Solution
Use `Classical.choose`:
```lean
noncomputable def archimedeanBound [IsArchimedean n] (a : FreeStarAlgebra n) : ℕ :=
  Classical.choose (IsArchimedean.bound a)

theorem archimedeanBound_spec [IsArchimedean n] (a : FreeStarAlgebra n) :
    ... ∈ QuadraticModule n :=
  Classical.choose_spec (IsArchimedean.bound a)
```

### Trade-off
- `Nat.find` gives the *minimal* witness
- `Classical.choose` gives *some* witness

For our purposes, existence of a bound is sufficient.

---

## Cyclic Vector Identity

### The Key Identity
`φ(a) = ⟨Ω, π(a)Ω⟩_ℝ`

Where:
- `Ω = coe'([1])` is the cyclic vector in the GNS Hilbert space
- `π(a)` is the GNS representation

### Proof Outline
1. `π(a)Ω = coe'([a])` by left multiplication: `π(a)[1] = [a*1] = [a]`
2. `⟨coe'([1]), coe'([a])⟩ = gnsInner [1] [a]` (completion preserves inner product)
3. `gnsInner [1] [a] = φ(star a * 1)` by definition
4. `= φ(star 1 * a)` by `sesqForm_symm`
5. `= φ(1 * a) = φ(a)` by `star_one` and `one_mul`

### Key Insight: gnsInner Order
The inner product is defined as `gnsInner (mk a) (mk b) = φ(star b * a)`.
So `gnsInner [1] [a] = φ(star a * 1)`, NOT `φ(star 1 * a)`.

We need `sesqForm_symm : φ(star a * b) = φ(star b * a)` to swap the order.

### File Reference
`AfTests/ArchimedeanClosure/GNS/CyclicIdentity.lean`:
- `gnsRep_cyclicVector` - π(a)(Ω) = coe'([a])
- `gnsRep_inner_cyclicVector` - ⟨Ω, π(a)Ω⟩_ℝ = φ(a)
