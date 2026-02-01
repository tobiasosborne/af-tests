# Handoff: 2026-02-01 (Session 114)

## Session Summary

**PROGRESS:** Diagnosed instance diamond issue in `primitive_peirce_one_dim_one`. The proof structure up to `hUnique` is COMPLETE and WORKING. Only the final `h_finrank_one` step is blocked.

**Result:** Build passes. 5 sorries in Primitive.lean.

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | **5** (Primitive.lean) |
| Build Status | **PASSING** |
| Blocker | Instance diamond in h_finrank_one |

---

## Proof Structure of `primitive_peirce_one_dim_one` (Primitive.lean:804)

The theorem proves: For primitive e, `finrank ℝ (PeirceSpace e 1) = 1`.

### What's WORKING (lines 815-923):

```
hle_span : PeirceSpace e 1 ≤ span{e}
├── letI R := P1PowerSubmodule_commRing    [line 819] ✓
├── haveI hArt : IsArtinianRing            [line 820] ✓
├── haveI hRed : IsReduced                 [line 822] ✓
├── let φ := artinian_reduced_is_product_of_fields  [line 825] ✓
└── hUnique : Unique (MaximalSpectrum P1PowerSubmodule)  [lines 833-923] ✓
    ├── Indicators ind I := φ⁻¹(Pi.single I 1)
    ├── Each ind I is Jordan-idempotent
    ├── By primitivity: (ind I).val = 0 or = e
    ├── Since ind I ≠ 0 (φ is iso): (ind I).val = e for all I
    ├── Orthogonality: ind I * ind J = 0 for I ≠ J
    └── If I ≠ J exist → jmul e e = 0, contradiction → Subsingleton
```

### What's BLOCKED (lines 929-934):

```lean
have h_finrank_one : Module.finrank ℝ ↥(P1PowerSubmodule e x) = 1 := by
  sorry  -- INSTANCE DIAMOND HERE
```

---

## The Instance Diamond Problem (DETAILED)

### The Setup

At line 819: `letI R := P1PowerSubmodule_commRing e x he.isIdempotent hx`
- This defines ring multiplication as `jmul` (see line 692)
- `letI` means it's a local definition, NOT automatically in typeclass search

### The Original Broken Code (before I sorried it)

```lean
have h_finrank_one : Module.finrank ℝ ↥(P1PowerSubmodule e x) = 1 := by
  haveI : Subsingleton (MaximalSpectrum ...) := inferInstance  -- Uses hUnique
  haveI hLocal : IsLocalRing := ...
  haveI hFieldI : IsField := ...
  haveI hField : Field := hFieldI.toField  -- ⚠️ CREATES NEW RING INSTANCE

  have hFR_P1 : ∀ m a, (∑ i, a i ^ 2) = 0 → ∀ i, a i = 0 := by
    intro m a hsum i
    -- Need: (a j ^ 2).val = jsq (a j).val
    -- But a j ^ 2 uses hField's multiplication!
    -- P1PowerSubmodule_npow_eq_jpow expects R's multiplication!
    ...
```

### The Type Error

```
Type mismatch:
  jmul ↑(a j) ↑(a j) = ↑(@HMul.hMul ... CommRing.toMul ... (a j) (a j))
but expected:
  jmul ↑(a j) ↑(a j) = ↑(@HMul.hMul ... Field.toMul ... (a j) (a j))
```

The multiplication from `CommRing R` and `Field hField` are **definitionally different** even though they compute the same thing.

---

## 🎯 CONCRETE FIX: Extract Formal Reality Lemma

### Approach 1: Prove formal reality BEFORE introducing Field

Create a standalone lemma that proves P1PowerSubmodule is formally real using ONLY the CommRing R:

```lean
/-- P1PowerSubmodule of a primitive idempotent is formally real. -/
lemma P1PowerSubmodule_formallyReal [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsPrimitive e) {x : J} (hx : x ∈ PeirceSpace e 1) :
    letI := P1PowerSubmodule_commRing e x he.isIdempotent hx
    ∀ (m : ℕ) (a : Fin m → ↥(P1PowerSubmodule e x)),
      (∑ i, a i ^ 2) = 0 → ∀ i, a i = 0 := by
  letI := P1PowerSubmodule_commRing e x he.isIdempotent hx
  intro m a hsum i
  -- Ring mul.val = jmul by definition
  have hmul_val : ∀ (b c : ↥(P1PowerSubmodule e x)), (b * c).val = jmul b.val c.val :=
    fun _ _ => rfl
  have hsum_val : ∑ j, jsq (a j).val = (0 : J) := by
    have h1 : (∑ j, a j ^ 2).val = 0 := by
      simp only [Submodule.coe_sum, ZeroMemClass.coe_zero]
      convert congrArg Subtype.val hsum
      apply Finset.sum_congr rfl
      intro j _
      rw [sq, hmul_val, jsq_def]
    exact h1
  exact Subtype.ext (FormallyRealJordan.sum_sq_eq_zero m (fun j => (a j).val) hsum_val i)
```

Then in `h_finrank_one`:
```lean
have h_finrank_one : Module.finrank ℝ ↥(P1PowerSubmodule e x) = 1 := by
  have hFR := P1PowerSubmodule_formallyReal he hx
  -- Now hFR uses the SAME CommRing instance as the rest of the proof
  haveI : Subsingleton (MaximalSpectrum ...) := inferInstance
  haveI hLocal : IsLocalRing := ...
  haveI hFieldI : IsField := ...
  -- DON'T use haveI for Field! Use the existing CommRing.
  obtain ⟨φ⟩ := formallyReal_field_is_real_commRing ↥(P1PowerSubmodule e x) hFR
  ...
```

### Approach 2: Use `@` to force instance

```lean
have hpow_eq : ∀ j, (@HPow.hPow _ _ _ (@instHPow _ _ (@Monoid.toNatPow _
    (@CommRing.toCommMonoid _ R))) (a j) 2).val = jsq (a j).val := ...
```

This is uglier but forces the correct instance.

### Approach 3: Change `letI R` to `haveI`

Line 819: Change `letI R := ...` to `haveI : CommRing ... := ...`
This puts R in typeclass search, so it might be preferred over the Field instance.

---

## Key Lemmas Needed

1. **`formallyReal_field_is_real`** (line 947 reference) - Check if this requires `Algebra ℝ` instance
   - Error showed: `failed to synthesize Algebra ℝ ↥(P1PowerSubmodule e x)`
   - May need to also prove P1PowerSubmodule has an ℝ-algebra structure

2. **`P1PowerSubmodule_npow_eq_jpow`** (line 714) - Already exists, connects ring power to jpow

---

## File Locations

| Item | Location |
|------|----------|
| `primitive_peirce_one_dim_one` | Primitive.lean:804 |
| `h_finrank_one` sorry | Primitive.lean:933 |
| `P1PowerSubmodule_commRing` | Primitive.lean:690 |
| `P1PowerSubmodule_npow_eq_jpow` | Primitive.lean:714 |
| `formallyReal_field_is_real` | FormallyReal/Properties.lean (search for it) |

---

## Other Sorries in Primitive.lean

| Line | Name | Status |
|------|------|--------|
| ~934 | `h_finrank_one` | BLOCKED by instance diamond |
| ~992 | `orthogonal_primitive_peirce_sq` | Needs `primitive_peirce_one_scalar` |
| ~1019 | `orthogonal_primitive_structure` | Needs above |
| ~1068 | `exists_primitive_decomp` | Needs induction design |
| ~1103 | `csoi_refine_primitive` | Needs `exists_primitive_decomp` |

---

## Session Commands Run

```bash
lake build           # Passes
git add ... && git commit -m "..."
bd create --title="Fix instance diamond in h_finrank_one proof" --type=bug --priority=1
bd sync && git push
```

---

## For Next Agent: Step-by-Step

1. **Read** Primitive.lean:690-750 to understand P1PowerSubmodule ring structure
2. **Search** for `formallyReal_field_is_real` to understand its signature and requirements
3. **Try Approach 1**: Create `P1PowerSubmodule_formallyReal` lemma OUTSIDE the main proof
4. **Test** if the instance diamond is resolved
5. If stuck on Algebra instance, check if P1PowerSubmodule needs explicit ℝ-algebra structure

**DO NOT** spend more than 3 attempts on the same approach. Document and move on.
