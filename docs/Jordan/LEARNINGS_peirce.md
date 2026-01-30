# Peirce Decomposition Learnings

## The Polynomial Identity

For an idempotent e in a Jordan algebra, the multiplication operator L_e satisfies:
```
L_e(L_e - ½)(L_e - 1) = 0
```

Equivalently: `L_e³ = (3/2)L_e² - (1/2)L_e`

This means L_e has eigenvalues only in {0, 1/2, 1}, giving the three Peirce spaces.

---

## Verification on Hermitian Matrices

For 2×2 symmetric matrices with e = diag(1,0), x = [[a,b],[b,c]]:
```
L_e(x) = [[a, b/2], [b/2, 0]]
L_e²(x) = [[a, b/4], [b/4, 0]]
L_e³(x) = [[a, b/8], [b/8, 0]]

L_e³ - (3/2)L_e² + (1/2)L_e =
  [[a - 3a/2 + a/2, b/8 - 3b/8 + b/4], ...] = 0 ✓
```

---

## Peirce Multiplication Rules (Theory)

For idempotent e with Peirce spaces P₀, P_{1/2}, P₁:

| × | P₀ | P_{1/2} | P₁ |
|---|----|---------|----|
| P₀ | P₀ | P_{1/2} | 0 |
| P_{1/2} | P_{1/2} | P₀⊕P₁ | P_{1/2} |
| P₁ | 0 | P_{1/2} | P₁ |

---

## Proof Difficulty

The Peirce rules require the Jordan **fundamental formula**:
```
U_{U_a(b)} = U_a U_b U_a
```
where `U_a(x) = 2a∘(a∘x) - a²∘x`.

This is non-trivial (~100+ LOC) to derive from the Jordan identity.

---

## Alternative: Linearized Jordan Identity

The identity `two_nsmul_lie_lmul_lmul_add_add_eq_zero` in mathlib gives:
```
2([L_a, L_{b∘c}] + [L_b, L_{c∘a}] + [L_c, L_{a∘b}]) = 0
```

This can be used to derive Peirce rules but requires careful case analysis.

---

## Current Implementation Status

### Completed
- `PeirceSpace e ev` definition and basic properties
- `peirceSpace_disjoint` - distinct eigenspaces are disjoint
- `idempotent_in_peirce_one` - e ∈ P₁(e)
- `complement_in_peirce_zero` - (1-e) ∈ P₀(e)

### Sorries (Need Fundamental Formula)
- `peirce_polynomial_identity` - L_e(L_e - 1/2)(L_e - 1) = 0
- `peirce_mult_P0_P0` - P₀ × P₀ ⊆ P₀
- `peirce_mult_P1_P1` - P₁ × P₁ ⊆ P₁
- `peirce_mult_P0_P1` - P₀ × P₁ = 0
- `peirce_mult_P12_P12` - P_{1/2} × P_{1/2} ⊆ P₀ ⊕ P₁
- `peirce_mult_P0_P12` - P₀ × P_{1/2} ⊆ P_{1/2}
- `peirce_mult_P1_P12` - P₁ × P_{1/2} ⊆ P_{1/2}

---

## References

- Hanche-Olsen & Størmer, *Jordan Operator Algebras*, Ch. 2
- McCrimmon, *A Taste of Jordan Algebras*, §2.8
