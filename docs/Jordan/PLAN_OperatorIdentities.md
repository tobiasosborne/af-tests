# Sorry Elimination Plan: OperatorIdentities.lean and Quadratic.lean

This document provides detailed analysis and step-by-step elimination plans for the
3 sorries in these files, focusing on how the linearized Jordan identity can be used
for operator manipulations.

---

## Overview of Sorries

| File | Theorem | Line | Goal |
|------|---------|------|------|
| OperatorIdentities.lean | `L_e_L_a_L_e` | 172 | `L e ∘ₗ L a ∘ₗ L e = L (jmul e (jmul a e)) + (1/2) • ⟦L e, ⟦L e, L a⟧⟧` |
| OperatorIdentities.lean | `opComm_double_idempotent` | 179 | `⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e))` |
| Quadratic.lean | `U_idempotent_comp` | 134 | `U e (U e x) = U e x` (for idempotent e) |

---

## Dependency Analysis

**Critical observation**: `L_e_L_a_L_e` and `opComm_double_idempotent` are *algebraically equivalent*.
If we prove one, the other follows by rearrangement.

```
L_e_L_a_L_e: L e ∘ₗ L a ∘ₗ L e = L(e(ae)) + (1/2)⟦L e, ⟦L e, L a⟧⟧

Rearranging: ⟦L e, ⟦L e, L a⟧⟧ = 2(L e ∘ₗ L a ∘ₗ L e - L(e(ae)))

This is exactly opComm_double_idempotent (with scalar distribution).
```

**Strategy**: Prove `opComm_double_idempotent` first, then derive `L_e_L_a_L_e`.

---

## Sorry 1: `opComm_double_idempotent` (OperatorIdentities.lean:177)

### Goal State

```lean
⊢ ⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e))
```

### Mathematical Analysis

The double commutator expands as:
```
⟦L e, ⟦L e, L a⟧⟧(x) = L e (⟦L e, L a⟧ x) - ⟦L e, L a⟧ (L e x)
                      = L e (L e (L a x) - L a (L e x)) - (L e (L a (L e x)) - L a (L e (L e x)))
                      = L e² L a x - L e L a L e x - L e L a L e x + L a L e² x
                      = L e² L a x + L a L e² x - 2 L e L a L e x
```

For idempotent e with e² = e:
```
= L e L a x + L a L e x - 2 L e L a L e x
= 2 L(e·(a·x)) - 2 L e L a L e x     [using jmul_comm and definitions]
```

Wait, this doesn't immediately match. Let me reconsider.

### Correct Mathematical Derivation

**Element-wise**, for idempotent e (he : jsq e = e, i.e., jmul e e = e):

```
⟦L e, ⟦L e, L a⟧⟧ x
  = e ∘ (e ∘ (a ∘ x) - a ∘ (e ∘ x)) - (e ∘ (a ∘ (e ∘ x)) - a ∘ (e ∘ (e ∘ x)))
```

Using he : jmul e e = e:
- jmul e (jmul e y) = jmul (jmul e e) y = jmul e y  [by fundamental_jordan']

Wait, that's not right either. Let me be more careful.

**Key insight**: Use `four_variable_identity` with appropriate substitutions.

From LinearizedJordan.lean, `four_variable_identity e e a x`:
```
e ∘ ((e ∘ a) ∘ x) + e ∘ ((a ∘ e) ∘ x) + a ∘ ((e ∘ e) ∘ x) =
(e ∘ a) ∘ (e ∘ x) + (a ∘ e) ∘ (e ∘ x) + (e ∘ e) ∘ (a ∘ x)
```

Using e ∘ e = e and jmul_comm:
```
2 ⋅ e ∘ ((e ∘ a) ∘ x) + a ∘ (e ∘ x) = 2 ⋅ (e ∘ a) ∘ (e ∘ x) + e ∘ (a ∘ x)
```

This gives us:
```
2 L e L(ea) x + L a L e x = 2 L(ea) L e x + L e L a x
```

Rearranging:
```
L e L a x - L a L e x = 2 L(ea) L e x - 2 L e L(ea) x
⟦L e, L a⟧ x = 2 ⟦L(ea), L e⟧ x
```

Hmm, this relates the single commutator to another commutator, not directly what we need.

### Alternative Approach: Direct Expansion

Let's compute `⟦L e, ⟦L e, L a⟧⟧(x)` directly:

```
⟦L e, ⟦L e, L a⟧⟧(x) = ⟦L e, L a⟧(e ∘ x) - e ∘ (⟦L e, L a⟧ x)      [skew of commutator]
                      ... wait, that's wrong. Let me be more careful.
```

Actually:
```
⟦L e, ⟦L e, L a⟧⟧ = L e ∘ ⟦L e, L a⟧ - ⟦L e, L a⟧ ∘ L e
```

And:
```
⟦L e, L a⟧ = L e ∘ L a - L a ∘ L e
```

So:
```
⟦L e, ⟦L e, L a⟧⟧ = L e ∘ (L e ∘ L a - L a ∘ L e) - (L e ∘ L a - L a ∘ L e) ∘ L e
                  = L e ∘ L e ∘ L a - L e ∘ L a ∘ L e - L e ∘ L a ∘ L e + L a ∘ L e ∘ L e
                  = L e² ∘ L a - 2 L e ∘ L a ∘ L e + L a ∘ L e²
```

For idempotent e with e² = e:
```
⟦L e, ⟦L e, L a⟧⟧ = L e ∘ L a + L a ∘ L e - 2 L e ∘ L a ∘ L e
```

Now we need: `L e ∘ L a + L a ∘ L e = 2 L(e(ae))`.

This would require: `e ∘ (a ∘ x) + a ∘ (e ∘ x) = 2 ⋅ (e ∘ (a ∘ e)) ∘ x`.

But wait, `e ∘ (a ∘ e)` is an element, not the same as the bilinear expression.

**The issue**: This identity is NOT true in general. Let me check H-O for the correct formula.

### H-O Source Check

From LEARNINGS.md Session 73:
> **NOT DIRECTLY IN H-O (need derivation or removal):**
> | `L_e_L_a_L_e` | OperatorIdentities.lean:170 | NOT in H-O - needs derivation from (2.35) or removal |
> | `opComm_double_idempotent` | OperatorIdentities.lean:177 | Circular with above |

**These theorems may be INCORRECT as stated!**

### Verification: Testing the Formula

Let's test with a concrete example. Take e = 1 (identity idempotent) in any Jordan algebra:
- LHS: ⟦L 1, ⟦L 1, L a⟧⟧ = ⟦id, ⟦id, L a⟧⟧ = ⟦id, 0⟧ = 0
- RHS: 2 L 1 ∘ L a ∘ L 1 - 2 L(1 ∘ (a ∘ 1)) = 2 L a - 2 L a = 0 ✓

That works. Let's try a non-trivial idempotent...

### Correct Formula Derivation

Using the expansion above:
```
⟦L e, ⟦L e, L a⟧⟧ = L e ∘ L a + L a ∘ L e - 2 L e ∘ L a ∘ L e   (for e² = e)
```

So the RHS of `opComm_double_idempotent` should be:
```
2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e))
```

For this to equal the LHS, we need:
```
L e ∘ L a + L a ∘ L e - 2 L e ∘ L a ∘ L e = 2 L e ∘ L a ∘ L e - 2 L(e(ae))
```

Simplifying:
```
L e ∘ L a + L a ∘ L e = 4 L e ∘ L a ∘ L e - 2 L(e(ae))
```

In element form at x:
```
e ∘ (a ∘ x) + a ∘ (e ∘ x) = 4 ⋅ e ∘ (a ∘ (e ∘ x)) - 2 ⋅ (e ∘ (a ∘ e)) ∘ x
```

This does NOT look like a standard Jordan identity. **The stated theorem may be incorrect.**

### Recommendation: VERIFY OR REMOVE

1. **Test with concrete Jordan algebra** (e.g., 2×2 symmetric matrices)
2. If false, **remove these theorems** or correct the formulas
3. If true but non-obvious, provide the correct H-O reference

---

## Step-by-Step Plan for `opComm_double_idempotent`

### Step 1: Verify the Formula (5 LOC)

```lean
-- Test in a concrete example first
example : let J := Matrix (Fin 2) (Fin 2) ℝ
          let e : J := !![1, 0; 0, 0]
          let a : J := !![1, 1; 1, 1]
          ⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e)) := by
  native_decide  -- or explicit computation
```

If this fails, the theorem statement is wrong.

### Step 2: If Valid, Prove via Direct Expansion (20-30 LOC)

```lean
theorem opComm_double_idempotent {e : J} (he : IsIdempotent e) (a : J) :
    ⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e)) := by
  -- Step 1: Expand the double commutator
  ext x
  simp only [opComm_apply, L_apply, LinearMap.smul_apply, LinearMap.comp_apply,
             LinearMap.sub_apply]
  -- Step 2: Use idempotent property he.jsq_eq_self
  have he' : jmul e e = e := by rw [← jsq_def]; exact he.jsq_eq_self
  -- Step 3: Apply jmul_jmul_e_x_e from Peirce.lean
  have hcomm : jmul (jmul e x) e = jmul e (jmul e x) := jmul_jmul_e_x_e he x
  -- Step 4: Expand and simplify using bilinearity
  rw [jmul_sub, jmul_sub, jmul_sub]
  simp only [jmul_sub, jmul_add, smul_sub]
  -- Step 5: Use he' to simplify e ∘ (e ∘ y) terms
  ...
  -- Step 6: Abel to combine terms
  abel
```

### Step 3: Alternative - Mark as Incorrect (2 LOC)

If Step 1 fails:
```lean
-- This theorem statement is INCORRECT. See LEARNINGS.md Session 73.
-- The correct identity needs to be derived from H-O Section 2.6.
theorem opComm_double_idempotent {e : J} (_he : IsIdempotent e) (a : J) :
    ⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e)) := by
  sorry  -- WONTFIX: Statement needs correction
```

---

## Sorry 2: `L_e_L_a_L_e` (OperatorIdentities.lean:170)

### Goal State

```lean
⊢ L e ∘ₗ L a ∘ₗ L e = L (jmul e (jmul a e)) + (1/2 : ℝ) • ⟦L e, ⟦L e, L a⟧⟧
```

### Dependency

This is the direct rearrangement of `opComm_double_idempotent`. If that theorem is proven:

```lean
theorem L_e_L_a_L_e {e : J} (he : IsIdempotent e) (a : J) :
    L e ∘ₗ L a ∘ₗ L e = L (jmul e (jmul a e)) + (1/2 : ℝ) • ⟦L e, ⟦L e, L a⟧⟧ := by
  have h := opComm_double_idempotent he a
  -- h : ⟦L e, ⟦L e, L a⟧⟧ = 2 • L e ∘ₗ L a ∘ₗ L e - 2 • L (jmul e (jmul a e))
  ext x
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, L_apply]
  -- Convert h to element form
  have hx := congrFun (congrArg DFunLike.coe h) x
  simp only [opComm_apply, L_apply, LinearMap.smul_apply, LinearMap.comp_apply,
             LinearMap.sub_apply] at hx
  -- Rearrange: LeaLe = L(e(ae)) + (1/2)⟦⟦⟧⟧
  -- From: ⟦⟦⟧⟧ = 2LeaLe - 2L(e(ae))
  -- Get: (1/2)⟦⟦⟧⟧ = LeaLe - L(e(ae))
  -- So: LeaLe = L(e(ae)) + (1/2)⟦⟦⟧⟧ ✓
  linarith  -- or module/field arithmetic
```

### Step-by-Step Plan (15 LOC)

Assuming `opComm_double_idempotent` is proven:

```lean
theorem L_e_L_a_L_e {e : J} (he : IsIdempotent e) (a : J) :
    L e ∘ₗ L a ∘ₗ L e = L (jmul e (jmul a e)) + (1/2 : ℝ) • ⟦L e, ⟦L e, L a⟧⟧ := by
  have h := opComm_double_idempotent he a
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  -- Rearrange h: ⟦L e, ⟦L e, L a⟧⟧ = 2 • (L e ∘ₗ L a ∘ₗ L e - L (jmul e (jmul a e)))
  rw [smul_sub] at h
  -- Get: (1/2) • ⟦⟧ = (L e ∘ₗ L a ∘ₗ L e) - L (jmul e (jmul a e))
  have h' : (1/2 : ℝ) • ⟦L e, ⟦L e, L a⟧⟧ = L e ∘ₗ L a ∘ₗ L e - L (jmul e (jmul a e)) := by
    rw [h]
    simp only [smul_smul]
    norm_num
  -- Rearrange to goal
  rw [← h']
  abel
```

---

## Sorry 3: `U_idempotent_comp` (Quadratic.lean:134)

### Goal State

```lean
⊢ U e (U e x) = U e x
```

Where `U a x = 2 • jmul a (jmul a x) - jmul (jsq a) x` and `he : IsIdempotent e`.

### Mathematical Analysis

For idempotent e with e² = e:
```
U e x = 2 ⋅ e ∘ (e ∘ x) - e ∘ x        [since jsq e = e]
```

Let y = U e x. Then:
```
U e y = 2 ⋅ e ∘ (e ∘ y) - e ∘ y
```

We need to show U e y = y, i.e.:
```
2 ⋅ e ∘ (e ∘ y) - e ∘ y = y
```

Substituting y = 2 ⋅ e ∘ (e ∘ x) - e ∘ x:
```
2 ⋅ e ∘ (e ∘ (2 ⋅ e ∘ (e ∘ x) - e ∘ x)) - e ∘ (2 ⋅ e ∘ (e ∘ x) - e ∘ x)
= 2 ⋅ e ∘ (e ∘ (2 ⋅ e ∘ (e ∘ x) - e ∘ x)) - e ∘ (2 ⋅ e ∘ (e ∘ x) - e ∘ x)
```

Using bilinearity and distributing:
```
= 4 ⋅ e ∘ (e ∘ (e ∘ (e ∘ x))) - 2 ⋅ e ∘ (e ∘ (e ∘ x)) - 2 ⋅ e ∘ (e ∘ (e ∘ x)) + e ∘ (e ∘ x)
= 4 ⋅ e ∘ (e ∘ (e ∘ (e ∘ x))) - 4 ⋅ e ∘ (e ∘ (e ∘ x)) + e ∘ (e ∘ x)
```

**Key Insight**: Use `peirce_polynomial_identity` from Peirce.lean:
```
2 L³_e - 3 L²_e + L_e = 0
```

This means: `2 ⋅ e ∘ (e ∘ (e ∘ z)) = 3 ⋅ e ∘ (e ∘ z) - e ∘ z`

Let z = e ∘ x:
```
2 ⋅ e ∘ (e ∘ (e ∘ (e ∘ x))) = 3 ⋅ e ∘ (e ∘ (e ∘ x)) - e ∘ (e ∘ x)
```

Let w = e ∘ (e ∘ x):
```
2 ⋅ e ∘ (e ∘ w) = 3 ⋅ e ∘ w - w
```

Substituting back:
```
4 ⋅ e ∘ (e ∘ (e ∘ (e ∘ x))) = 2 ⋅ (3 ⋅ e ∘ (e ∘ (e ∘ x)) - e ∘ (e ∘ x))
                            = 6 ⋅ e ∘ (e ∘ (e ∘ x)) - 2 ⋅ e ∘ (e ∘ x)
```

So our expression becomes:
```
= (6 ⋅ e ∘ (e ∘ (e ∘ x)) - 2 ⋅ e ∘ (e ∘ x)) - 4 ⋅ e ∘ (e ∘ (e ∘ x)) + e ∘ (e ∘ x)
= 2 ⋅ e ∘ (e ∘ (e ∘ x)) - e ∘ (e ∘ x)
= 2 ⋅ e ∘ (e ∘ (e ∘ x)) - e ∘ (e ∘ x)
```

Now apply Peirce polynomial to e ∘ x again:
```
2 ⋅ e ∘ (e ∘ (e ∘ x)) = 3 ⋅ e ∘ (e ∘ x) - e ∘ x
```

So:
```
= (3 ⋅ e ∘ (e ∘ x) - e ∘ x) - e ∘ (e ∘ x)
= 2 ⋅ e ∘ (e ∘ x) - e ∘ x
= y ✓
```

### Step-by-Step Implementation Plan (30-40 LOC)

```lean
theorem U_idempotent_comp (e : J) (he : IsIdempotent e) :
    U_linear e ∘ₗ U_linear e = U_linear e := by
  ext x
  simp only [LinearMap.comp_apply, U_linear_apply]
  -- Goal: U e (U e x) = U e x

  -- Step 1: Expand U definitions
  simp only [U_def]
  have he' : jmul e e = e := by rw [← jsq_def]; exact he.jsq_eq_self
  simp only [jsq_def, he']
  -- Now goal is in terms of nested jmul only

  -- Step 2: Define shorthand for L_e^n(x)
  set L1 := jmul e x with hL1
  set L2 := jmul e L1 with hL2
  set L3 := jmul e L2 with hL3
  set L4 := jmul e L3 with hL4

  -- Step 3: Apply Peirce polynomial identity
  -- 2 L³_e = 3 L²_e - L_e
  have peirce := peirce_polynomial_identity he x
  -- peirce : 2 • L3 = 3 • L2 - L1 (in smul form)

  -- Step 4: Derive 4 L⁴_e = 6 L³_e - 2 L²_e
  have peirce_L2 := peirce_polynomial_identity he (jmul e x)
  -- gives: 2 • L4 = 3 • L3 - L2

  -- Step 5: Expand and substitute
  -- y = U e x = 2 • L2 - L1
  -- U e y = 2 • L_e(L_e y) - L_e y
  --       = 2 • L_e(L_e(2L2 - L1)) - L_e(2L2 - L1)
  --       = 2 • (2 L_e³ x - L_e² x) - (2 L_e² x - L_e x)
  --       = 4 L³ - 2 L² - 2 L² + L = 4 L³ - 4 L² + L

  -- Step 6: Use Peirce: 2 L³ = 3 L² - L, so 4 L³ = 6 L² - 2 L
  -- 4 L³ - 4 L² + L = 6 L² - 2 L - 4 L² + L = 2 L² - L = y ✓

  -- Actual Lean proof:
  simp only [jmul_sub, smul_sub, jmul_smul, smul_jmul]
  -- The key calculation using bilinearity
  have h4L3 : (4 : ℝ) • L4 = (6 : ℝ) • L3 - (2 : ℝ) • L2 := by
    have := peirce_L2
    simp only [two_smul] at this ⊢
    linarith -- or convert using smul arithmetic

  -- Final combination using abel/module
  ...
  module
```

### Key Lemma Needed

The proof uses `peirce_polynomial_identity` which states:
```lean
theorem peirce_polynomial_identity {e : J} (he : IsIdempotent e) (x : J) :
    2 • jmul e (jmul e (jmul e x)) - 3 • jmul e (jmul e x) + jmul e x = 0
```

This is already proven in Peirce.lean (lines 126-188).

---

## Linearized Jordan Toolbox

The following lemmas from LinearizedJordan.lean are available for operator manipulations:

| Lemma | Statement | Use Case |
|-------|-----------|----------|
| `four_variable_identity` | a((bc)d) + b((ca)d) + c((ab)d) = (bc)(ad) + (ca)(bd) + (ab)(cd) | General 4-variable identity |
| `operator_formula` | L_a L_{bc} + L_b L_{ca} + L_c L_{ab} = L_{a(bc)} + L_b L_a L_c + L_c L_a L_b | Operator composition |
| `L_L_jsq_comm` | Commute (L a) (L (jsq a)) | Power associativity |
| `fundamental_jordan` | (a² ∘ b) ∘ a = a² ∘ (b ∘ a) | Jordan identity variant |
| `jpow_add` | aᵐ ∘ aⁿ = aᵐ⁺ⁿ | Power associativity |

And from Peirce.lean for idempotent-specific work:

| Lemma | Statement | Use Case |
|-------|-----------|----------|
| `peirce_polynomial_identity` | 2L³_e - 3L²_e + L_e = 0 | Idempotent eigenvalue structure |
| `jmul_jmul_e_x_e` | (e ∘ x) ∘ e = e ∘ (e ∘ x) | Idempotent commutativity |
| `peirce_mult_P1_P1` | P₁(e) × P₁(e) ⊆ P₁(e) | Peirce 1-space closure |

---

## Summary and Priority

| Sorry | Priority | Difficulty | LOC | Notes |
|-------|----------|------------|-----|-------|
| `opComm_double_idempotent` | HIGH | MEDIUM | 25 | Need to VERIFY formula first |
| `L_e_L_a_L_e` | HIGH | LOW | 15 | Follows from above |
| `U_idempotent_comp` | MEDIUM | MEDIUM | 35 | Uses Peirce polynomial |

**Recommended Order:**
1. Verify `opComm_double_idempotent` formula with concrete example
2. If valid, prove it using direct expansion
3. Derive `L_e_L_a_L_e` algebraically
4. Prove `U_idempotent_comp` using Peirce polynomial identity

**Total Estimated LOC:** 75-85

---

## CRITICAL WARNING

From LEARNINGS.md Session 73:
> `L_e_L_a_L_e` and `opComm_double_idempotent` are **NOT DIRECTLY IN H-O** and need
> derivation from (2.35) or removal.

Before implementing, **verify the theorems are correct** by testing on concrete examples.
If incorrect, update LEARNINGS.md and either correct the formulas or mark as WONTFIX.
