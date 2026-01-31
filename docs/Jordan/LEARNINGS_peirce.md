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

## Implementation Status (COMPLETE ✅)

All Peirce multiplication rules are proven using `four_variable_identity`.

### Proven Theorems
- `peirce_polynomial_identity` - L_e(L_e - 1/2)(L_e - 1) = 0 ✅
- `peirce_mult_P0_P0` - P₀ × P₀ ⊆ P₀ ✅
- `peirce_mult_P1_P1` - P₁ × P₁ ⊆ P₁ ✅
- `peirce_mult_P0_P1` - P₀ × P₁ = 0 ✅
- `peirce_mult_P12_P12` - P_{1/2} × P_{1/2} ⊆ P₀ ⊕ P₁ ✅
- `peirce_mult_P0_P12` - P₀ × P_{1/2} ⊆ P_{1/2} ✅
- `peirce_mult_P1_P12` - P₁ × P_{1/2} ⊆ P_{1/2} ✅

---

## Proof Techniques

### Core Tool: `four_variable_identity` (H-O 2.34)

```
a ∘ ((b∘c) ∘ d) + b ∘ ((c∘a) ∘ d) + c ∘ ((a∘b) ∘ d)
  = (b∘c) ∘ (a∘d) + (c∘a) ∘ (b∘d) + (a∘b) ∘ (c∘d)
```

Substituting idempotent e and Peirce eigenvectors gives constraints on products.

### P₀ × P₀ ⊆ P₀ (Direct)
Use `four_variable_identity e e a b` with e∘a = e∘b = 0:
- Most terms vanish → `0 = e∘(a∘b)`

### P₁ × P₁ ⊆ P₁ (Direct)
Use `four_variable_identity e e a b` with e∘a = a, e∘b = b:
- Algebra gives `e∘(a∘b) = a∘b`

### P₀ × P₁ = 0 (Orthogonality)
Most complex case. For c = a∘b with a ∈ P₀, b ∈ P₁:
1. `four_variable_identity e a b e` → `L_e²(c) = L_e(c) - c`
2. Iterate → `L_e³(c) = -c`
3. Peirce polynomial `2L³ - 3L² + L = 0` → `c = 2L_e(c)`
4. Compute `L_e²(c)` two ways → `(3/4)c = 0` → `c = 0`

### P₀ × P_{1/2} and P₁ × P_{1/2} ⊆ P_{1/2}
Use `four_variable_identity a e e b`:
- With eigenvalue conditions, most terms simplify
- Direct eigenvalue algebra gives L_e(c) = (1/2)c

### P_{1/2} × P_{1/2} ⊆ P₀ ⊕ P₁
For c = a∘b with a, b ∈ P_{1/2}:
1. `four_variable_identity e a b e` with eigenvalue simplifications
2. Derive `L_e²(c) = L_e(c)` (idempotent action on product)
3. Decompose: c = (c - L_e(c)) + L_e(c)
   - L_e(c - L_e(c)) = 0 ⟹ (c - L_e(c)) ∈ P₀
   - L_e(L_e(c)) = L_e(c) ⟹ L_e(c) ∈ P₁
4. Use `Submodule.mem_sup` to conclude c ∈ P₀ ⊔ P₁

---

## Key Lean Patterns

### Scalar multiplication
- `jmul_smul r a b : jmul (r • a) b = r • jmul a b`
- `smul_jmul r a b : jmul a (r • b) = r • jmul a b`

### Submodule supremum
```lean
rw [Submodule.mem_sup]
refine ⟨x₀, hx₀_mem, x₁, hx₁_mem, hsum⟩
```

### Module element arithmetic
- Use `abel` instead of `ring` (no associativity)
- Use `calc` chains with explicit rewrites
- `sub_eq_zero.mpr` / `sub_eq_zero.mp` for equality ↔ subtraction

---

## References

- Hanche-Olsen & Størmer, *Jordan Operator Algebras*, Ch. 2
- McCrimmon, *A Taste of Jordan Algebras*, §2.8
