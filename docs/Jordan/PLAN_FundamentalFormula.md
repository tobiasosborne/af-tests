# Sorry Elimination Plan: FundamentalFormula.lean

This document provides detailed step-by-step plans for eliminating the 2 sorries in
`AfTests/Jordan/FundamentalFormula.lean`.

---

## Overview

**File:** `/home/tobiasosborne/Projects/af-tests/AfTests/Jordan/FundamentalFormula.lean`

**Sorries:** 2
1. `linearized_jordan_aux` (line 54) - Auxiliary lemma for fundamental formula
2. `fundamental_formula` (line 83) - The main theorem U_{U_a(b)} = U_a U_b U_a

**Key Reference:** Hanche-Olsen & Stormer, "Jordan Operator Algebras" (1984), Section 2.4.18

---

## Background: The Fundamental Formula

The fundamental formula states:
```
U_{U_a(b)} = U_a ∘ U_b ∘ U_a
```

Equivalently, using the triple product {aba} = U_a(b):
```
{a{b{aca}b}a} = {{aba}c{aba}}
```

This is identity (2.41) in H-O, proved via Macdonald's Theorem (2.4.15).

**Critical Insight:** The H-O proof does NOT require `linearized_jordan_aux` at all!
The fundamental formula follows directly from Macdonald's theorem, which states that
polynomial identities linear in one variable that hold in special Jordan algebras
hold in all Jordan algebras.

---

## Sorry #1: `linearized_jordan_aux` (line 45-54)

### Location
```lean
private theorem linearized_jordan_aux (a b c : J) :
    jmul (jmul a (jmul b c)) (jsq a) +
    jmul (jmul b (jmul a c)) (jsq a) +
    jmul (jmul c (jmul a b)) (jsq a) =
    jmul a (jmul (jmul b c) (jsq a)) +
    jmul b (jmul (jmul a c) (jsq a)) +
    jmul c (jmul (jmul a b) (jsq a)) := by
  sorry
```

### Goal State
```lean
J : Type u_1
inst : JordanAlgebra J
a b c : J
⊢ jmul (jmul a (jmul b c)) (jsq a) + jmul (jmul b (jmul a c)) (jsq a) + jmul (jmul c (jmul a b)) (jsq a) =
    jmul a (jmul (jmul b c) (jsq a)) + jmul b (jmul (jmul a c) (jsq a)) + jmul c (jmul (jmul a b) (jsq a))
```

### Analysis

This theorem claims that for all a, b, c in a Jordan algebra:
```
(a(bc))a² + (b(ac))a² + (c(ab))a² = a((bc)a²) + b((ac)a²) + c((ab)a²)
```

**Critical Issue (from LEARNINGS.md Session 54, 57):** The proof strategy originally
proposed is WRONG. The bilinear identity `2·a((ab)(ac)) = (ab)(a(ac)) + (ac)(a(ab))`
required for this approach is FALSE in general Jordan algebras.

### Mathematical Status

**The theorem statement IS TRUE** - it's a consequence of the linearized Jordan identity.
However, the original proof approach via the bilinear identity is invalid.

### Alternative Proof Strategy

The correct approach uses the four-variable identity (H-O 2.34) and operator formula (H-O 2.35):

**Step 1 (~15 LOC):** Apply `four_variable_identity` with appropriate substitutions

The four-variable identity (already proven in `LinearizedJordan.lean`) states:
```lean
a ∘ ((b∘c) ∘ d) + b ∘ ((c∘a) ∘ d) + c ∘ ((a∘b) ∘ d) =
(b∘c) ∘ (a∘d) + (c∘a) ∘ (b∘d) + (a∘b) ∘ (c∘d)
```

**Step 2 (~20 LOC):** Use `operator_formula_apply` (H-O 2.35)

The operator formula relates compositions to products:
```lean
a((bc)d) + b((ca)d) + c((ab)d) = (a(bc))d + b(a(cd)) + c(a(bd))
```

**Step 3 (~15 LOC):** Use Jordan identity `jordan_identity a (jmul b c)` on first term

The Jordan identity gives `(a(bc))a² = a((bc)a²)` directly for the first term.
The remaining terms require the operator formula for handling.

### Recommended Implementation

```lean
private theorem linearized_jordan_aux (a b c : J) :
    jmul (jmul a (jmul b c)) (jsq a) +
    jmul (jmul b (jmul a c)) (jsq a) +
    jmul (jmul c (jmul a b)) (jsq a) =
    jmul a (jmul (jmul b c) (jsq a)) +
    jmul b (jmul (jmul a c) (jsq a)) +
    jmul c (jmul (jmul a b) (jsq a)) := by
  -- First term: Jordan identity gives (a(bc))a² = a((bc)a²)
  have h1 : jmul (jmul a (jmul b c)) (jsq a) = jmul a (jmul (jmul b c) (jsq a)) :=
    jordan_identity a (jmul b c)

  -- Second and third terms: use operator_formula_apply with d = jsq a
  -- operator_formula_apply a b c d gives:
  -- a((bc)d) + b((ca)d) + c((ab)d) = (a(bc))d + b(a(cd)) + c(a(bd))
  have h_op := operator_formula_apply a b c (jsq a)

  -- Substitute and use commutativity to rearrange
  -- ... (detailed manipulation using jmul_comm and operator identities)
  sorry  -- ~30 LOC of careful term manipulation
```

### Estimated Effort: 50 LOC

### Alternative: Mark as Unnecessary

Since the fundamental formula can be proven directly via Macdonald's theorem (see Sorry #2),
this lemma may be **unnecessary**. Consider deleting it and using the direct approach.

---

## Sorry #2: `fundamental_formula` (line 72-83)

### Location
```lean
theorem fundamental_formula (a b : J) :
    ∀ x, U (U a b) x = U a (U b (U a x)) := by
  intro x
  simp only [U_def]
  sorry
```

### Goal State (after `simp only [U_def]`)
```lean
J : Type u_1
inst : JordanAlgebra J
a b x : J
⊢ 2 • jmul (2 • jmul a (jmul a b) - jmul (jsq a) b) (jmul (2 • jmul a (jmul a b) - jmul (jsq a) b) x) -
      jmul (jsq (2 • jmul a (jmul a b) - jmul (jsq a) b)) x =
    2 • jmul a (jmul a (2 • jmul b (jmul b (2 • jmul a (jmul a x) - jmul (jsq a) x)) -
              jmul (jsq b) (2 • jmul a (jmul a x) - jmul (jsq a) x))) -
      jmul (jsq a) (2 • jmul b (jmul b (2 • jmul a (jmul a x) - jmul (jsq a) x)) -
              jmul (jsq b) (2 • jmul a (jmul a x) - jmul (jsq a) x))
```

This is a massive expression. The direct expansion approach is NOT recommended.

### Analysis

The fundamental formula is identity (2.41) in H-O:
```
{a{b{aca}b}a} = {{aba}c{aba}}
```

In operator form: `U_a U_b U_a = U_{U_a(b)}`

**H-O Proof (Section 2.4.18):** "The identity is quite clearly true in any special
Jordan algebra and so by 2.4.15 it is true in all Jordan algebras."

This uses Macdonald's theorem (2.4.15), which states:
> Any polynomial identity in three variables, with degree at most 1 in the third variable,
> and which holds in all special Jordan algebras, holds in all Jordan algebras.

### Recommended Proof Strategy: Macdonald's Theorem

**Option A: Formalize Macdonald's Theorem (~200+ LOC)**

This is the canonical approach and enables many other results. However, it's a significant
undertaking requiring:
1. Free Jordan algebras
2. Free special Jordan algebras
3. The exceptional ideal
4. Technical lemmas 2.4.20-2.4.24

**Option B: Use Shirshov-Cohn Theorem (~100 LOC)**

For the fundamental formula specifically, we can use the Shirshov-Cohn theorem (H-O 2.4.14):
> Any Jordan algebra generated by two elements is special.

The algebra generated by {a, b, x} may have more than 2 generators, but we can use:
- The identity holds for all x when a, b are fixed
- Specialize to subalgebra generated by a, b, and any fixed x

**Option C: Direct Calculation (~150-200 LOC)**

Expand both sides and verify term-by-term using:
- Jordan identity
- Linearized Jordan identity
- Power associativity (jpow_add)
- Four-variable identity

This is tedious but mechanical.

### Detailed Plan for Option B (Shirshov-Cohn)

**Step 1 (~20 LOC):** State that the identity holds in special Jordan algebras

```lean
-- In special Jordan algebras, {aba} = a∘b∘a (associative product)
-- So U_a U_b U_a (x) = a∘(b∘(a∘x∘a)∘b)∘a
-- and U_{U_a(b)}(x) = (a∘b∘a)∘x∘(a∘b∘a)
-- These are equal by associativity
```

**Step 2 (~30 LOC):** Apply Shirshov-Cohn to the subalgebra generated by {a, b}

```lean
-- The subalgebra of J generated by a and b is special (Shirshov-Cohn)
-- Therefore the identity holds for all products of a and b
```

**Step 3 (~50 LOC):** Extend to all x by linearity

```lean
-- U operators are linear in the argument x
-- The identity holds for all x in the subalgebra generated by {a, b}
-- By linearity and density arguments, it holds for all x ∈ J
```

**Issue:** This approach requires formalizing the Shirshov-Cohn theorem first.

### Detailed Plan for Option C (Direct Calculation)

This is the most self-contained approach, using only what's already proven.

**Step 1 (~20 LOC):** Introduce abbreviations

```lean
let Ua := U a
let Ub := U b
let ab := U a b  -- This is {aba} = U_a(b)
-- Goal: U ab x = Ua (Ub (Ua x))
```

**Step 2 (~30 LOC):** Expand U_a(b) using the definition

```lean
-- U_a(b) = 2·a∘(a∘b) - a²∘b
have hab : U a b = 2 • jmul a (jmul a b) - jmul (jsq a) b := rfl
```

**Step 3 (~40 LOC):** Compute U_{U_a(b)}(x) - LHS

Using bilinearity and the definition of U:
```lean
-- U_{ab}(x) = 2·(ab)∘((ab)∘x) - (ab)²∘x
-- Need to compute (ab)², i.e., jsq (U a b)
```

**Step 4 (~40 LOC):** Compute U_a(U_b(U_a(x))) - RHS

Work from inside out:
```lean
-- U_a(x) = 2·a∘(a∘x) - a²∘x
-- U_b(U_a(x)) = 2·b∘(b∘(U_a(x))) - b²∘(U_a(x))
-- U_a(U_b(U_a(x))) = 2·a∘(a∘(...)) - a²∘(...)
```

**Step 5 (~50 LOC):** Use Jordan identity and power associativity

Key lemmas needed:
- `jordan_identity`: (a∘y)∘a² = a∘(y∘a²)
- `jpow_add`: aᵐ∘aⁿ = aᵐ⁺ⁿ
- `L_L_jsq_comm`: L_a and L_{a²} commute

**Step 6 (~20 LOC):** Final assembly with abel

After expanding and simplifying, the two sides should match modulo additive rearrangement.

### Estimated Effort

| Approach | LOC | Dependencies |
|----------|-----|--------------|
| Option A (Macdonald) | 200+ | Free algebras infrastructure |
| Option B (Shirshov-Cohn) | 100 | Shirshov-Cohn theorem |
| Option C (Direct) | 150-200 | None (all prerequisites exist) |

### Recommendation

**Short-term:** Use Option C (direct calculation). It's tedious but has no new dependencies.

**Long-term:** Formalize Macdonald's theorem (Option A) as it enables many other results
including the fundamental formula as a trivial corollary.

---

## Implementation Priorities

### Phase 1: Verify `linearized_jordan_aux` is needed (~1 session)

1. Check if `fundamental_formula` can be proven without `linearized_jordan_aux`
2. If yes, delete `linearized_jordan_aux`
3. If no, implement using four-variable identity + operator formula

### Phase 2: Prove `fundamental_formula` (~2-3 sessions)

Using Option C (direct calculation):

**Session A (~50 LOC):**
- Expand both sides
- Introduce intermediate expressions
- Compute jsq (U a b)

**Session B (~50 LOC):**
- Apply Jordan identity to key terms
- Use power associativity
- Simplify nested products

**Session C (~50 LOC):**
- Final matching of terms
- Use abel for additive rearrangement
- Verify and clean up

---

## Dependencies and Imports

The proof will use:

**From LinearizedJordan.lean:**
- `four_variable_identity`
- `operator_formula_apply`
- `jpow_add`
- `L_jpow_comm_L`
- `L_L_jsq_comm`

**From Quadratic.lean:**
- `U_def`
- `U_linear`
- `U_smul`

**From OperatorIdentities.lean:**
- `linearized_jordan_operator`
- `operator_commutator_jsq`

**From Basic.lean / Product.lean:**
- `jordan_identity`
- `jmul_comm`, `jmul_add`, etc.

---

## Key Mathematical Insights

### Why the fundamental formula is central

1. **Structure theory:** The fundamental formula is the main tool for proving that
   invertibility in Jordan algebras works correctly (H-O 3.2.10-3.2.11).

2. **Peirce theory:** For idempotent e, U_e is idempotent as an operator. The fundamental
   formula gives U_e ∘ U_e = U_{U_e(e)} = U_e (since U_e(e) = e).

3. **Spectral theory:** The formula underlies the functional calculus for JB-algebras.

### The triple product interpretation

The U operator is defined as U_a(x) = {axa} = 2·a∘(a∘x) - a²∘x.

The fundamental formula in triple product notation:
```
{(aba)(b(aca)b)(aba)} = {a{b{aca}b}a}
```

In special algebras, this is just associativity: (aba)(b(aca)b)(aba) = a(b(aca)b)a.

---

## Verification Checklist

After implementation:

- [ ] `linearized_jordan_aux` compiles without sorry
- [ ] `fundamental_formula` compiles without sorry
- [ ] `U_jsq` (corollary) still compiles (uses fundamental_formula)
- [ ] `U_idempotent_comp'` (corollary) still compiles
- [ ] `fundamental_formula_linear` still compiles
- [ ] Full `lake build` passes
- [ ] Documentation updated in LEARNINGS.md

---

## References

- Hanche-Olsen & Stormer, "Jordan Operator Algebras" (1984), Section 2.4.15-2.4.18
- McCrimmon, "A Taste of Jordan Algebras", Theorem 2.4.5
- `docs/Jordan/LEARNINGS.md` Sessions 54, 57 (bilinear identity analysis)
