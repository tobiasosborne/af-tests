# Handoff: 2026-02-02 (Session 50)

## Completed This Session

### New Helper Lemmas (Primitive.lean:1372-1393)

Added key lemmas for combining orthogonal decompositions:

1. **sub_idem_orthog_of_orthog**: If f ⊥ g and p is a sub-idempotent of f (jmul f p = p), then p ⊥ g
   - Uses: orthogonal_in_peirce_zero, peirce_mult_P0_P1

2. **sub_idem_orthog_of_sum_orthog**: If f ⊥ g, p₁ ≤ f, p₂ ≤ g, then p₁ ⊥ p₂
   - Key for combining primitive decompositions of orthogonal idempotents

### exists_primitive_decomp Progress

All helper infrastructure is now in place:
- `sub_idem_finrank_lt`: finrank decreases for sub-idempotents ✅
- `sub_idem_orthog_of_sum_orthog`: primitives from orthogonal parts are orthogonal ✅

**Remaining work** (issue af-3fx6):
- Set up strong induction on `finrank P₁(e)` using `Nat.strong_induction_on`
- Combine decompositions using `Fin.append` and `Fin.addCases`
- The recursive structure and all key lemmas are ready

---

## Previous Session (49)

### Helper Lemmas for exists_primitive_decomp (Primitive.lean:1367-1412)

Added key lemmas enabling induction on finrank P₁(e):

1. **sub_idem_in_peirce_one**: If `jmul e f = f`, then `f ∈ P₁(e)`

2. **orthog_idem_peirce_one_le**: For orthogonal idempotents f, g: `P₁(f) ≤ P₁(f+g)`
   - Key insight: g ∈ P₀(f) implies `jmul g x = 0` for x ∈ P₁(f) by `peirce_mult_P0_P1`

3. **orthog_idem_peirce_one_lt**: For orthogonal f, g with g ≠ 0: `P₁(f) < P₁(f+g)`
   - Witness: g ∈ P₁(f+g) but g ∉ P₁(f) (since jmul f g = 0 ≠ g)

4. **sub_idem_finrank_lt**: `finrank P₁(f) < finrank P₁(e)` when `e = f + g` orthogonal

---

## Previous Session (48)

### Issue Cleanup

Closed stale issues for theorems that are fully proven:
- `af-w3sf`: primitive_peirce_one_dim_one (Primitive.lean:865-1064)
- `af-fbx8`, `af-utz0`: Same theorem, stale references
- `af-vaoe`: orthogonal_primitive_peirce_sq (Primitive.lean:1134)
- `af-eb7o`: orthogonal_primitive_structure (Primitive.lean:1287)

---

## Previous Session (47)

### ✅ isPrimitive_of_peirce_one_dim_one (Primitive.lean:1069-1100)

Added converse of `primitive_peirce_one_dim_one`:
```lean
theorem isPrimitive_of_peirce_one_dim_one {e : J} (he : IsIdempotent e) (hne : e ≠ 0)
    (hdim : Module.finrank ℝ (PeirceSpace e 1) = 1) : IsPrimitive e
```

**Key insight**: P₁(e) = ℝ·e when dim = 1. Any sub-idempotent f ∈ P₁(e) satisfies f = r • e.
Then jsq f = f gives r² = r, so r ∈ {0, 1}, hence f = 0 or f = e → e is primitive.

**Combined with `primitive_peirce_one_dim_one`**: Now have bidirectional characterization:
- `e primitive ⟺ finrank P₁(e) = 1`

This unblocks the induction approach for `exists_primitive_decomp`.

---

## Previous Session (46)

### ✅ Peirce Space Convenience Lemmas (Peirce.lean:47-53)

Added simp lemmas to simplify Peirce membership for eigenvalues 0 and 1:
- `mem_peirceSpace_zero_iff`: `a ∈ PeirceSpace e 0 ↔ jmul e a = 0`
- `mem_peirceSpace_one_iff`: `a ∈ PeirceSpace e 1 ↔ jmul e a = a`

### Closed Issues
- `af-0ysg`: Fix Peirce space eigenvalue form

---

## Previous Session (45)

### ✅ FormallyRealTrace Instance (Matrix/Trace.lean)

Added `formallyRealTraceHermitianMatrix` instance with:
- `traceReal_jsq_nonneg`: `0 ≤ traceReal (jsq A)`
- `traceReal_jsq_eq_zero_iff`: `traceReal (jsq A) = 0 ↔ A = 0`

Key helper: `traceReal_jsq_eq_traceInnerReal A : traceReal (jsq A) = traceInnerReal A A`

### ✅ orthogonal_primitive_structure (Primitive.lean:1251-1289)

Proved the H-O 2.9.4(iv) dichotomy:
```lean
theorem orthogonal_primitive_structure {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f) :
    (∀ a, jmul e a = (1/2) • a → jmul f a = (1/2) • a → a = 0) ∨
    IsStronglyConnected e f
```

**Proof strategy**:
- Case 1: All a in Peirce½(e) ∩ Peirce½(f) are zero → left disjunct
- Case 2: ∃ nonzero a → by `orthogonal_primitive_peirce_sq`, `jsq a = μ • (e+f)` with μ ≥ 0
  - μ > 0 (else jsq a = 0 ⟹ a = 0 by formal reality)
  - Let v = (√μ)⁻¹ • a, then jsq v = e + f → strongly connected

### Closed Issues
- `af-5zpv`: JordanTrace instance complete
- `af-2dzb`: trace_L_selfadjoint proven
- `af-pxqu`: FormallyRealTrace instance complete
- `af-xg63`: orthogonal_primitive_structure proven

---

## Previous Session (44)

### ✅ JordanTrace Instance Complete (Matrix/Trace.lean)

**Filled** two sorries in `AfTests/Jordan/Matrix/Trace.lean`:

1. **traceReal_smul** (line 220): `traceReal (r • A) = r * traceReal A`
2. **traceReal_L_selfadjoint** (line 252): `Tr((A∘V)∘W) = Tr(V∘(A∘W))`

**Result**: `jordanTraceHermitianMatrix` instance has no sorries.

---

## Previous Session (43)

### ✅ orthogonal_primitive_peirce_sq COMPLETE

**Completed** Step 12 (final step) in `Primitive.lean:1213-1244`:

- **Step 12**: `0 ≤ r₁` (non-negativity via formal reality)
  - Strategy: prove by contradiction using `FormallyRealJordan.sum_sq_eq_zero`
  - If `r₁ < 0`: form `jsq a + jsq (√(-r₁) • (e+f)) = 0` using `jsq_smul_idem hef_idem`
  - By formal reality, both summands are zero
  - `√(-r₁) • (e+f) = 0` with `√(-r₁) ≠ 0` implies `e + f = 0`
  - But `e + f = 0` contradicts orthogonality (would need `jmul e (-e) = 0`, i.e., `e = 0`)

**Key lemmas used**:
- `jsq_smul_idem he : jsq (r • e) = r² • e` (for idempotent e)
- `Real.sq_sqrt` - `(√x)² = x` for x ≥ 0
- `FormallyRealJordan.sum_sq_eq_zero` - formal reality property
- `smul_eq_zero`, `eq_neg_of_add_eq_zero_left`

**The theorem is now fully proven (12/12 steps, no sorry)!**

---

## Previous Session (42)

### Step 11: orthogonal_primitive_peirce_sq (r₁ = r₂)

**Added** Step 11 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1153-1212`:

- **Step 11**: `hr_eq : r₁ = r₂` (coefficient equality)
  - Key technique: Use Jordan identity `jordan_identity' a e` (and `jordan_identity' a f`)
  - Derive `jmul a (jsq a) = r₁ • a` and `jmul a (jsq a) = r₂ • a`
  - Conclude `(r₁ - r₂) • a = 0`, use `smul_eq_zero` to case split
  - If `a ≠ 0`: direct `linarith`
  - If `a = 0`: show `r₁ = r₂ = 0` via linear independence of orthogonal primitives

**Key lemmas used**:
- `jordan_identity' a e : jmul (jmul a e) (jsq a) = jmul a (jmul e (jsq a))`
- `jmul_smul`, `smul_jmul` - scalar pulling for Jordan product
- `smul_comm` - commutativity of scalar multiplication
- `smul_right_injective J h12ne` - injectivity when scalar ≠ 0
- `smul_eq_zero` - r • x = 0 ↔ r = 0 ∨ x = 0

---

## Previous Session (41)

### Steps 7-10: orthogonal_primitive_peirce_sq

**Added** Steps 7-10 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1133-1153`:

- **Step 7**: `hef_idem : IsIdempotent (e + f)`
- **Step 8**: `ha_in_P1_ef : a ∈ PeirceSpace (e + f) 1`
- **Step 9**: `hsq_in_P1_ef : jsq a ∈ PeirceSpace (e + f) 1`
- **Step 10**: `hsq_decomp : jsq a = r₁ • e + r₂ • f`

---

## Previous Session (40)

### Step 6: orthogonal_primitive_peirce_sq

**Added** Step 6 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1124-1131`:
- `hc₀e_zero : jmul e c₀e = 0` (c₀e ∈ P₀(e))
- `hjmul_e_sq : jmul e (jsq a) = r₁ • e` (symmetric to Step 5, using e-decomposition)

**Technique Note**: When rewriting with `IsIdempotent` (which is `jsq e = e`), need
to first convert `jmul e e` to `jsq e` using `← jsq_def` since `rw` doesn't unfold definitions.

---

## Previous Session (39)

### Helper Lemma: orthogonal_sum_isIdempotent

**Added** to `AfTests/Jordan/FormallyReal/Spectrum.lean:99-107`:
- `orthogonal_sum_isIdempotent` - sum of orthogonal idempotents is idempotent
- Required for Step 7 of `orthogonal_primitive_peirce_sq` proof

**Added** Step 4 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1113-1114`:
- `hf_in_P0_e : f ∈ PeirceSpace e 0` using `orthogonal_in_peirce_zero`
- `he_in_P0_f : e ∈ PeirceSpace f 0` using `orthogonal_in_peirce_zero horth.symm`

**Added** Step 5 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1116-1122`:
- `hjmul_f_sq : jmul f (jsq a) = r₂ • f`
- Uses f-decomposition and `c₀f ∈ P₀(f)` implies `jmul f c₀f = 0`

---

## Previous Session (38)

### JordanAlgebra Instance: Matrix/Instance.lean

**Created** `AfTests/Jordan/Matrix/Instance.lean` (126 LOC) with:
- `RealSymmetricMatrix` type alias for `selfAdjoint (Matrix n n ℝ)`
- `JordanAlgebra (RealSymmetricMatrix n)` instance

**Also added to JordanProduct.lean:**
- `jordanMul_add` - bilinearity (right)
- `add_jordanMul` - bilinearity (left)
- `smul_jordanMul` - scalar multiplication (left)
- `jordanMul_smul` - scalar multiplication (right)
- `jordan_identity` - the Jordan identity for matrices

**Key proof technique for Jordan identity:**
```lean
simp only [smul_add, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
conv_lhs => simp only [Matrix.mul_assoc]
conv_rhs => simp only [Matrix.mul_assoc]
ring_nf; abel
```

---

## Current State

### Jordan Algebra Project
- 9 files, ~870 LOC total
- **1 sorry remaining:**
  - `FormallyReal/Def.lean` - `of_sq_eq_zero` (requires spectral theory)
- Matrix Jordan algebra now has full instance

### Archimedean Closure Project: COMPLETE
- 44 files, 4,943 LOC, 0 sorries

---

## Next Steps

### Immediate (unblocked tasks)
1. `af-j4dq`: Jordan/FormallyReal/Spectrum.lean - Spectral properties
2. `af-dc2h`: Jordan/Matrix/RealHermitian.lean - Additional properties
3. `af-noad`: Jordan/FormallyReal/Square.lean - Square roots

### Deferred
- `af-0xrg`: of_sq_eq_zero - needs architectural decision (spectral theory vs axioms)
- `af-tpm2`: Spectral theory development (P3)

---

## Files Modified This Session

- `AfTests/Jordan/Matrix/JordanProduct.lean` (added bilinearity, Jordan identity)
- `AfTests/Jordan/Matrix/Instance.lean` (NEW - JordanAlgebra instance)
- `HANDOFF.md` (updated)

---

## Sorries

1. `AfTests/Jordan/FormallyReal/Def.lean:58-68` - `of_sq_eq_zero`
   - Proving: single-element property implies sum-of-squares property
   - Status: **Requires spectral theory or ordering axioms**
   - See: Faraut-Korányi "Analysis on Symmetric Cones"

---

## Technical Notes

### Jordan Identity Proof Pattern
The Jordan identity `(A ∘ B) ∘ A² = A ∘ (B ∘ A²)` for matrices:
1. Expand using `jordanMul_def` and `jordanMul_self`
2. Pull scalars through with `smul_mul_assoc`, `mul_smul_comm`
3. Apply `Matrix.mul_assoc` using `conv` to both sides
4. Terms become identical after `ring_nf; abel`

### HermitianMatrix vs RealSymmetricMatrix
- `HermitianMatrix n R` works for general `[Field R] [StarRing R]`
- `RealSymmetricMatrix n` = `selfAdjoint (Matrix n n ℝ)` has `Module ℝ` automatically
- Only RealSymmetricMatrix gets JordanAlgebra instance (over ℝ)

---

## Beads Summary

- 1 task closed this session: `af-dcxu` (JordanAlgebra instance)

---

## Previous Sessions

### Session 37 (2026-01-30)
- Eliminated IsHermitian.jordanMul sorry
- Documented of_sq_eq_zero limitation

### Session 36 (2026-01-30)
- Jordan FormallyReal properties, cone, matrix product (3 files, 269 LOC)

### Session 35 (2026-01-30)
- Jordan algebra core infrastructure (5 files, 460 LOC)
