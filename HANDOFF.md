# Handoff: 2026-02-01 (Session 115)

## Session Summary

**PROGRESS:** Added three new helper lemmas to support h_finrank_one proof:
- `P1PowerSubmodule_formallyReal` - proves formal reality using CommRing
- `P1PowerSubmodule_algebra` - defines ℝ-algebra structure
- `P1PowerSubmodule_finiteDimensional` - finite dimensionality

**Blocker:** Instance diamond between `Algebra.toModule` and `Submodule.module` prevents applying `formallyReal_field_is_real`.

**Result:** Build passes. 5 sorries in Primitive.lean.

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | **5** (Primitive.lean) |
| Build Status | **PASSING** |
| Blocker | Module instance diamond in h_finrank_one |

---

## The Instance Diamond Problem (Session 115 Update)

### New Lemmas Added (all compile ✅)

1. **`P1PowerSubmodule_formallyReal`** (line ~791)
   - Proves: `∀ m a, (∑ i, a i ^ 2) = 0 → ∀ i, a i = 0`
   - Uses ONLY CommRing R, avoids Field diamond
   - Key: `(a ^ 2).val = jsq a.val` via `P1PowerSubmodule_npow_eq_jpow` + `jpow_two`

2. **`P1PowerSubmodule_algebra`** (line ~754)
   - Defines: `Algebra ℝ ↥(P1PowerSubmodule e x)`
   - Uses `Algebra.ofModule` with `jmul_smul` and `smul_jmul`

3. **`P1PowerSubmodule_finiteDimensional`** (line ~778)
   - Proves: `FiniteDimensional ℝ ↥(P1PowerSubmodule e x)`
   - Simple: submodule of finite-dimensional space

### The Remaining Block

When calling `formallyReal_field_is_real`:
```
Application type mismatch:
  hFD has type FiniteDimensional ... (P1PowerSubmodule e x).module
  but expected    FiniteDimensional ... Algebra.toModule
```

The two module structures:
- `(P1PowerSubmodule e x).module` - inherited from J as submodule
- `Algebra.toModule` - derived from `P1PowerSubmodule_algebra`

**They are mathematically equal** (both give `r • x` for scalar `r` and element `x`), but Lean can't unify them.

---

## Fix Approaches for Next Agent

### Approach A: Prove Module Structures are Defeq
Show that `Algebra.toModule = Submodule.module` for P1PowerSubmodule:
```lean
theorem P1PowerSubmodule_module_eq (e x : J) (he : IsIdempotent e) (hx : x ∈ PeirceSpace e 1) :
    letI := P1PowerSubmodule_commRing e x he hx
    letI := P1PowerSubmodule_algebra e x he hx
    @Algebra.toModule ℝ _ _ _ (P1PowerSubmodule_algebra e x he hx) =
      (P1PowerSubmodule e x).module := rfl  -- May need proof
```

### Approach B: Direct φ : P1PowerSubmodule ≃+* ℝ
Since hUnique gives a single maximal ideal, use φ directly:
```lean
-- φ : P1PowerSubmodule ≃+* ((I : MaximalSpectrum) → P1PowerSubmodule/I)
-- With Unique MaximalSpectrum, this is P1PowerSubmodule ≃+* F for single field F
-- F is formally real → F ≅ ℝ → compose to get P1PowerSubmodule ≃+* ℝ
```

### Approach C: Alternative Finrank Argument
Use the quotient F directly:
```lean
-- F = P1PowerSubmodule / maximalIdeal
-- But for a local field, maximalIdeal = {0}
-- So P1PowerSubmodule ≅ F as rings
-- F formally real + finite-dim over ℝ → F = ℝ
-- finrank ↥(P1PowerSubmodule) = finrank F = 1
```

---

## Proof Structure of `primitive_peirce_one_dim_one` (Primitive.lean:836)

### What's WORKING (lines 847-963):

```
hle_span : PeirceSpace e 1 ≤ span{e}
├── letI R := P1PowerSubmodule_commRing    [line 851] ✓
├── haveI hArt : IsArtinianRing            [line 852] ✓
├── haveI hRed : IsReduced                 [line 854] ✓
├── let φ := artinian_reduced_is_product_of_fields  [line 857] ✓
├── hUnique : Unique (MaximalSpectrum P1PowerSubmodule)  [lines 865-955] ✓
├── hLocal : IsLocalRing (from hUnique)    [line 998] ✓
└── hIsField : IsField (Artinian+Reduced+Local)  [line 1004] ✓
```

### What's BLOCKED (line ~1009):

```lean
have h_finrank_one : Module.finrank ℝ ↥(P1PowerSubmodule e x) = 1 := by
  -- Have: hIsField, hField (Field instance)
  -- Have: P1PowerSubmodule_formallyReal, P1PowerSubmodule_algebra
  -- Block: Module instance mismatch when calling formallyReal_field_is_real
  sorry
```

---

## Other Sorries in Primitive.lean

| Line | Name | Status |
|------|------|--------|
| ~1009 | `h_finrank_one` | BLOCKED by module instance diamond |
| ~1053 | `orthogonal_primitive_peirce_sq` | Needs `primitive_peirce_one_scalar` |
| ~1080 | `orthogonal_primitive_structure` | Needs above |
| ~1129 | `exists_primitive_decomp` | Needs induction design |
| ~1164 | `csoi_refine_primitive` | Needs `exists_primitive_decomp` |

---

## File Locations

| Item | Location |
|------|----------|
| `primitive_peirce_one_dim_one` | Primitive.lean:836 |
| `h_finrank_one` sorry | Primitive.lean:~1009 |
| `P1PowerSubmodule_commRing` | Primitive.lean:690 |
| `P1PowerSubmodule_formallyReal` | Primitive.lean:791 |
| `P1PowerSubmodule_algebra` | Primitive.lean:754 |
| `formallyReal_field_is_real` | Primitive.lean:101 |

---

## For Next Agent: Step-by-Step

1. **Read** the new lemmas at lines 754-822 to understand what's been built
2. **Try Approach A**: Check if the module structures are definitionally equal
3. **If not defeq**, try Approach B or C
4. **Max 3 attempts** on any single approach, then checkpoint

**DO NOT** delete the new lemmas. They compile and represent progress.
