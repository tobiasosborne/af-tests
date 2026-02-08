# Handoff: 2026-02-08 (Session 128)

## What was done this session
- **Deep analysis** of the sorry at line 160 of `eq258_xCons_yCons_lt` in Equation258.lean
- **Identified the exact missing lemma**: `T_{x^l} ∘ U_{x^m} = U_{x^m} ∘ T_{x^l}` (L commutes with U for powers of same element)
- **Found H-O justification**: H-O line 1197 states "by 2.4.5, T_xT_z = T_zT_x and U_xT_z = T_zU_x" for x,z powers of same element
- **Worked out complete proof strategy** with concrete code steps (see below)
- No code changes this session — all analysis/planning

## IMMEDIATE NEXT: Fill sorry at line 160 of Equation258.lean

### Concrete code steps for next agent

**File**: `AfTests/Jordan/Macdonald/Equation258.lean`, theorem `eq258_xCons_yCons_lt`

**Task**: Replace lines 147-160 (from `-- Step 4:` through `sorry`) with working proof.

#### Step-by-step proof plan

The goal at line 146 (after `simp only [T_apply] at hge ⊢`) is:
```
⊢ mul(x^{k+1})(U_bi(x^{i+1},y^{j+1})(v)) =
    ½(U_bi(x^{k+1+i+1},y^{j+1})(v) +
      U(x^{i+1})(2•mul(x^{k-i})(mul(y^{j+1})(v)) - U_bi(y^{j+1},x^{k-i})(v)))
```
with h247v at T/U_bi level and hge at mul/U_bi level.

**Replace lines 147-160 with this proof structure:**

```lean
  -- Step 4: Prove T(x^l) commutes with U(x^m) for powers of same element
  -- H-O line 1197: "by 2.4.5, U_xT_z = T_zU_x" when x,z powers of same element
  -- Proof: U = 2L² - L_{a²}, and L_jpow_comm_all gives L-operator commutation
  have hTU : ∀ w : FreeJordanAlg,
      mul (pow x (k - i)) (U (pow x (i + 1)) w) =
      U (pow x (i + 1)) (mul (pow x (k - i)) w) := by
    intro w
    simp only [U]
    -- Goal: mul(x^l)(2•mul(x^m)(mul(x^m)(w)) - mul(mul(x^m)(x^m))(w))
    --     = 2•mul(x^m)(mul(x^m)(mul(x^l)(w))) - mul(mul(x^m)(x^m))(mul(x^l)(w))
    -- where l = k-i, m = i+1
    -- Need: mul distributes over sub and smul
    -- NOTE: no mul_sub_right lemma exists! Use: a∘(b-c) = a∘(b+(-c)) = a∘b + a∘(-c) = a∘b - a∘c
    -- via mul_add_right + show (-x) = (-1)•x + smul_mul_right
    have hc : ∀ w', mul (pow x (k - i)) (mul (pow x (i + 1)) w') =
        mul (pow x (i + 1)) (mul (pow x (k - i)) w') := by
      intro w'
      have := (JordanAlgebra.L_jpow_comm_all (J := FreeJordanAlg)
        FreeJordanAlg.x (k - i) (i + 1)).eq
      simp only [FJ_L_apply, FJ_jpow_eq_pow] at this
      exact congrFun (congrArg DFunLike.coe this) w'
    have hpow : mul (pow x (i + 1)) (pow x (i + 1)) = pow x (i + 1 + (i + 1)) := by
      rw [← FJ_jmul_eq_mul, ← FJ_jpow_eq_pow, ← FJ_jpow_eq_pow, ← FJ_jpow_eq_pow]
      exact (JordanAlgebra.jpow_add FreeJordanAlg.x (i + 1) (i + 1)).symm
    have hc2 : ∀ w', mul (pow x (k - i)) (mul (pow x (i + 1 + (i + 1))) w') =
        mul (pow x (i + 1 + (i + 1))) (mul (pow x (k - i)) w') := by
      intro w'
      have := (JordanAlgebra.L_jpow_comm_all (J := FreeJordanAlg)
        FreeJordanAlg.x (k - i) (i + 1 + (i + 1))).eq
      simp only [FJ_L_apply, FJ_jpow_eq_pow] at this
      exact congrFun (congrArg DFunLike.coe this) w'
    -- Distribute mul over (2•A - B) = (A + A - B)
    simp only [two_smul]
    rw [mul_add_right, mul_add_right]  -- distribute outer mul
    -- Now rewrite with hpow to normalize mul(x^m)(x^m) to pow x (2m)
    rw [← hpow]  -- or rw [hpow] depending on direction, match goal shape
    -- Apply hc twice (to commute x^l past x^m) and hc2 once (for x^{2m})
    -- Use conv or rw for targeted application to avoid simp loops
    rw [hc, hc w]
    rw [show mul (pow x (k - i)) (mul (mul (pow x (i + 1)) (pow x (i + 1))) w) =
      mul (mul (pow x (i + 1)) (pow x (i + 1))) (mul (pow x (k - i)) w) from by
      rw [hpow, hc2, ← hpow]]
  -- Step 5: Use h245 (power_formula_245) to get U_bi(x^{i+1},x^{k+1}) = T(x^{k-i})∘U(x^{i+1})
  have h245 := @JordanAlgebra.power_formula_245 FreeJordanAlg _
    FreeJordanAlg.x (mul (pow y (j + 1)) v) (k - i) (i + 1) (i + 1)
  simp only [JordanAlgebra.triple_def, FJ_jmul_eq_mul, FJ_jpow_eq_pow] at h245
  rw [show i + 1 + (k - i) = k + 1 from by omega] at h245
  -- h245: 2•mul(x^{k-i})(U_bi(x^{i+1},x^{i+1})(w)) = U_bi(x^{k+1},x^{i+1})(w) + U_bi(x^{i+1},x^{k+1})(w)
  -- Since U_bi_self: U_bi(a,a) = U(a), and U_bi_comm: U_bi(a,b) = U_bi(b,a):
  simp only [U_bilinear_self] at h245  -- fold U_bi(x^{i+1},x^{i+1}) = U(x^{i+1})
  rw [U_bilinear_comm (pow x (k + 1)) (pow x (i + 1))] at h245
  -- h245: 2•mul(x^{k-i})(U(x^{i+1})(w)) = 2•U_bi(x^{i+1},x^{k+1})(w)
  -- Halve: mul(x^{k-i})(U(x^{i+1})(w)) = U_bi(x^{i+1},x^{k+1})(w)
  -- With hTU: U_bi(x^{i+1},x^{k+1})(w) = U(x^{i+1})(mul(x^{k-i})(w))
  have hkey : U_bilinear (pow x (i + 1)) (pow x (k + 1)) (mul (pow y (j + 1)) v) =
      U (pow x (i + 1)) (mul (pow x (k - i)) (mul (pow y (j + 1)) v)) := by
    -- From h245: 2•T∘U = 2•U_bi, so T∘U = U_bi
    -- From hTU: T∘U = U∘T, so U_bi = U∘T
    have h1 : mul (pow x (k - i)) (U (pow x (i + 1)) (mul (pow y (j + 1)) v)) =
        U_bilinear (pow x (i + 1)) (pow x (k + 1)) (mul (pow y (j + 1)) v) := by linarith
    rw [← h1, hTU]
  -- Step 6: Substitute hge into h247v, then use hkey to close
  simp only [T_apply] at h247v
  rw [hge] at h247v
  -- h247v: LHS + ½(U_bi(x^{i+1+k+1}) + U(x^{i+1})(U_bi(x^{k-i},y^{j+1})(v)))
  --      = U_bi(x^{i+1},x^{k+1})(mul(y^{j+1})(v)) + U_bi(x^{k+1+i+1},y^{j+1})(v)
  rw [show i + 1 + k + 1 = k + 1 + i + 1 from by omega] at h247v
  -- Now solve for LHS from h247v and substitute hkey
  -- LHS = hkey_result + ½U_bi(x^{k+1+i+1}) - ½U(x^{i+1})(U_bi(x^{k-i}))
  -- Goal RHS = ½U_bi(x^{k+1+i+1}) + ½U(x^{i+1})(2T - U_bi(y,x^{k-i}))
  -- Use U_bilinear_comm: U_bi(y,x^{k-i}) = U_bi(x^{k-i},y)
  -- Then ½U(2T - U_bi) = U(T) - ½U(U_bi) via U linearity (U_add_right, U_smul_right)
  -- With hkey: U(T) = U_bi, so it all cancels
  -- Close with linarith or algebra after expanding U linearity
  sorry  -- THIS sorry should now close with the above setup
```

#### Key insights that make this work

1. **The missing lemma** (H-O 2.4.5, line 1197): `T_{x^l} ∘ U_{x^m} = U_{x^m} ∘ T_{x^l}`
   - Proof: expand U = 2L² - L_{a²}, use `L_jpow_comm_all` (proven in LinearizedJordan.lean:340)
   - Use `mul_add_right` + `smul_mul_right` to distribute (no `mul_sub_right` exists)

2. **From power_formula_245**: `T(x^{k-i}) ∘ U(x^{i+1}) = U_bi(x^{i+1}, x^{k+1})`
   - Combine with commutation: `U_bi(x^{i+1}, x^{k+1}) = U(x^{i+1}) ∘ T(x^{k-i})`

3. **The proof closes** because after substituting hge and hkey into h247v:
   - The U_bi(x^{k+1+i+1}) terms combine (½ + ½ = 1, cancel)
   - The U(x^{i+1})(U_bi(x^{k-i})) terms cancel (using U_bi_comm: U_bi(y,x) = U_bi(x,y))
   - Leaves: U_bi(x^{i+1},x^{k+1})(w) = U(x^{i+1})(T(x^{k-i})(w)) — which is hkey ✓

#### Available lemmas (all compiled, no imports needed)
- `L_jpow_comm_all` (LinearizedJordan.lean:340): `Commute (L (jpow a l)) (L (jpow a m))`
- `FJ_L_apply`, `FJ_jpow_eq_pow`, `FJ_jmul_eq_mul` (FJOperators.lean:173-186): bridge lemmas
- `U_bilinear_self` (FJOperators.lean:84): `U_bi(a,a)(v) = U(a)(v)`
- `U_bilinear_comm` (FJOperators.lean:94): `U_bi(a,b)(v) = U_bi(b,a)(v)`
- `mul_add_right` (FJOperators.lean:115): `mul a (b + c) = mul a b + mul a c`
- `smul_mul_right` (FJOperators.lean:125): `mul a (r • b) = r • mul a b`
- `U` (FJOperators.lean, @[simp]): expands `JordanAlgebra.U a v` to `2 • mul a (mul a v) - mul (mul a a) v`
- `U_add_right` (Quadratic.lean:79): `U a (x + y) = U a x + U a y`
- `U_smul_right` (Quadratic.lean:85): `U a (r • x) = r • U a x`
- `jpow_add` (OperatorId.lean:69): `jpow a (m+n) = jmul (jpow a m) (jpow a n)`

#### Potential pitfalls
- **No `mul_sub_right`**: use `show (-x) = (-1 : ℝ) • x` + `smul_mul_right` + `mul_add_right`
- **`simp only [hc]` may loop** for commutation: use `rw [hc]` or `conv` instead
- **`hpow` needed**: `mul(x^m)(x^m)` is NOT `pow x (2m)` syntactically — must prove via `jpow_add`
- **Index arithmetic**: `i + 1 + k + 1 = k + 1 + i + 1` needs `omega`

#### Validation after fix
```bash
lake env lean AfTests/Jordan/Macdonald/Equation258.lean 2>&1 | grep -E "error|sorry"
lake build AfTests 2>&1 | tail -40
bd close af-2n2o && bd sync
git add AfTests/Jordan/Macdonald/Equation258.lean && git commit -m "eq258_xCons_yCons_lt: fill sorry via T∘U commutation" && git push && bd sync
```

---

## State of the codebase
- Equation258.lean: **compiles** (0 errors, 3 sorries — 1 in eq258_xCons_yCons_lt, 2 in weight>1 cases)
- PropertyI.lean: compiles (sorry at line 540)
- MOperatorProperties.lean: compiles
- Macdonald.lean: 3 sorries (mult_alg_surjectivity, macdonald, fundamental_formula_general)

## Critical path: 3 sorries → 0

```
af-2n2o: Fix Eq258 sorry ──→ af-0llu/af-iobv: Eq258 weight>1 sorry fills
                                     │
                                     ↓
                          af-mlnv: GenLemma+Surj ──→ af-0cc6: mult_alg_surj
                                                                  │
af-opkm/af-fddm: Property (i) ──────────────────────────────────→│
                                                                  ↓
                                                    af-g2kb: Macdonald theorem
                                                                  │
                                                                  ↓
                                                    af-gzm1: fundamental_formula
```

## Previous Sessions

### Session 128 (this): Deep analysis of eq258_xCons_yCons_lt sorry — identified T∘U commutation lemma
### Session 127: Fixed Eq258 Error 1, diagnosed Error 2 (mul_comm canonicalization)
### Session 126: Fixed 9 of 11 Eq258 compilation errors
### Session 125: MOperatorProperties fixes + Equation258 issue
### Session 124: Parallel agent session (3 tasks, no code changes — context limits)
### Session 123: Eq(2.58) weight>1 framework (~170 LOC, 2 sorries at algebra closure)
### Session 122b: evalAssoc naturality + M_op_evalAssoc bridge
### Session 121b: Property (i) — gamma_mac algebraic identities
### Session 121: eq258_xCons_yCons_lt (weight<=1 i<k case, sorry-free)
### Session 120: eq258_xCons_yCons_ge + M_op_U_prependY fill
### Session 119: Property (iii) general x-version + FJ_U_pow_comp
### Session 118: H-O audit, dead code deletion
### Session 117-110: Earlier infrastructure work
