# Non-Commutative Proof Patterns

## Pattern 1: Expansion in Non-Commutative Algebras

When `ring` doesn't work (non-commutative), use:
```lean
simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
abel
```

**Used in**: `CauchySchwarzM.lean:65`

---

## Pattern 2: Additive Simplification

When you need `x + y + ... = n • z` in a non-commutative ring:
```lean
have h : expr = (n : ℕ) • z := by abel
rw [h, nsmul_eq_mul, Nat.cast_ofNat, ...]
```

**Example**: Proving `(1 + x) + (1 - x) = 2`:
```lean
have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
  have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
  rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
```

---

## Pattern 3: Scalar Multiplication Cancellation

When you need `(a : ℝ) • ((b : R) * x) = (a * b) • x`:
```lean
have h : (b : R) * x = (b : ℝ) • x := by rw [Algebra.smul_def]; rfl
rw [h, smul_smul]
norm_num  -- simplifies scalar arithmetic
```

**Example**: `(1/4) • (4 * x) = x`:
```lean
have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
  rw [Algebra.smul_def]; rfl
rw [h_scalar, smul_smul]
norm_num  -- (1/4) * 4 = 1
```

---

## Pattern 4: Commutativity in Non-Commutative Rings

Build `Commute a b` hypotheses using:
- `Commute.one_left`, `Commute.one_right` (unit commutes)
- `Commute.refl` (self-commutation)
- `Commute.add_left`, `Commute.add_right` (distribute over +)
- `Commute.sub_left`, `Commute.sub_right` (distribute over -)
- `Commute.neg_left`, `Commute.neg_right` (negation)

Then use `Commute.mul_self_sub_mul_self_eq`, `Commute.add_sq`, etc.

---

## Case Study: selfAdjoint_decomp

### The Identity
For self-adjoint `x`: `x = ¼(1+x)² - ¼(1-x)²`

### Why ring Fails
- `ring` assumes commutativity
- `FreeAlgebra` is non-commutative

### The Key Insight: Commute Lemmas
`(1+x)` and `(1-x)` commute because `1` commutes with everything and `x` commutes with itself.

### Building the Commute Hypothesis
```lean
have hcomm : Commute (1 + x) (1 - x) := by
  apply Commute.add_left
  · exact (Commute.one_left _).sub_right (Commute.one_left x)
  · exact (Commute.one_right x).sub_right (Commute.refl x)
```

**Breakdown**:
1. `Commute (1 + x) (1 - x)` splits via `add_left`
2. `Commute 1 (1-x)` splits via `sub_right` into `one_left` cases
3. `Commute x (1-x)` splits via `sub_right` into `one_right` and `refl`

### Complete Proof
```lean
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := by
  -- Simplify star terms using self-adjointness
  have h1 : star (1 + x) = 1 + x := (isSelfAdjoint_one_add hx).star_eq
  have h2 : star (1 - x) = 1 - x := (isSelfAdjoint_one_sub hx).star_eq
  rw [h1, h2]
  -- Factor out (1/4) scalar
  rw [← smul_sub]
  -- Build Commute hypothesis and apply difference of squares
  have hcomm : Commute (1 + x) (1 - x) := by
    apply Commute.add_left
    · exact (Commute.one_left _).sub_right (Commute.one_left x)
    · exact (Commute.one_right x).sub_right (Commute.refl x)
  rw [hcomm.mul_self_sub_mul_self_eq]
  -- Simplify sums and differences
  have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
    have h : ... = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
    have h : ... = (2 : ℕ) • x := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sum_eq, diff_eq]
  -- Scalar cancellation
  simp only [← mul_assoc]
  have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
  rw [h_four]
  have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
    rw [Algebra.smul_def]; rfl
  rw [h_scalar, smul_smul]
  norm_num
```

---

## Key Mathlib Lemmas Reference

| Lemma | Purpose |
|-------|---------|
| `Commute.one_left` | 1 commutes left |
| `Commute.one_right` | 1 commutes right |
| `Commute.refl` | Self-commutativity |
| `Commute.add_left/right` | Sum commutes |
| `Commute.sub_left/right` | Difference commutes |
| `Commute.mul_self_sub_mul_self_eq` | Diff of squares |
| `smul_sub` | `a•p - a•q = a•(p-q)` |
| `smul_smul` | `a•(b•x) = (a*b)•x` |
| `nsmul_eq_mul` | `(n:ℕ)•x = n*x` |
| `Algebra.smul_def` | `c•a = algebraMap c * a` |

---

## Pattern 5: AlgebraMap Commutation

When proving `φ(star b * (r • a)) = r * φ(star b * a)` for r : ℝ:

```lean
-- r • a = algebraMap r * a
rw [Algebra.smul_def]
-- Now have: φ(star b * (algebraMap r * a))
-- Use ← mul_assoc to get: φ((star b * algebraMap r) * a)
rw [← mul_assoc]
-- Use Algebra.commutes to move algebraMap r: algebraMap r * x = x * algebraMap r
rw [← Algebra.commutes r (star b)]
-- Now have: φ((algebraMap r * star b) * a)
rw [mul_assoc, ← Algebra.smul_def, φ.map_smul]
```

**Key insight**: `Algebra.commutes` says the image of the base ring is in the center.

**Used in**: `GNS/Quotient.lean:gnsInner_smul_left`

---

## Why Previous Approaches Failed

1. **Direct `ring`**: Non-commutative algebra
2. **Manual expansion with simp**: Works but scalars messy
3. **Calc chains with `(4 : ℝ)⁻¹`**: Type inference issues
4. **Using `add_smul` directly**: Module instance resolution problems
