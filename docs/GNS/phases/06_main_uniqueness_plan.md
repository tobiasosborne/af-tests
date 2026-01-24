# GNS Uniqueness Completion Plan

## Overview

Complete the GNS uniqueness theorem, which states that the GNS representation is
unique up to unitary equivalence. The current implementation has:
- `gnsIntertwinerQuotientFun` - the map U₀ : gnsQuotient → H
- `gnsIntertwinerQuotient_isometry` - proves ‖U₀(x)‖ = ‖x‖
- `gnsIntertwinerQuotient_cyclic` - proves U₀([1]) = ξ

## Missing Components

1. Linearity of U₀
2. Wrap as LinearIsometry on quotient
3. Extension to full Hilbert space H_φ
4. Surjectivity (using cyclicity)
5. LinearIsometryEquiv construction
6. Intertwining property
7. Final theorem statement

## Granular Implementation Steps

Each step is ≤50 LOC to add to `Main/Uniqueness.lean` or a new file.

---

### Step 1: Linearity of U₀ (~45 LOC)
**File:** `Main/Uniqueness.lean` (append)
**Beads ID:** `af-tests-aov`

```lean
/-- U₀ preserves addition. -/
theorem gnsIntertwinerQuotient_add
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x y : φ.gnsQuotient) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state (x + y) =
    gnsIntertwinerQuotientFun φ π ξ hξ_state x +
    gnsIntertwinerQuotientFun φ π ξ hξ_state y

/-- U₀ preserves scalar multiplication. -/
theorem gnsIntertwinerQuotient_smul
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (c : ℂ) (x : φ.gnsQuotient) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state (c • x) =
    c • gnsIntertwinerQuotientFun φ π ξ hξ_state x

/-- U₀ maps zero to zero. -/
theorem gnsIntertwinerQuotient_zero
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state 0 = 0
```

**Proof sketch:**
- For add: Use that π is additive, Quotient.liftOn behavior
- For smul: Use that π is a star algebra hom (hence ℂ-linear)
- For zero: Use that π(0) = 0

---

### Step 2: LinearMap structure (~35 LOC)
**File:** `Main/Uniqueness.lean` (append)
**Beads ID:** `af-tests-6tj`

```lean
/-- U₀ as a linear map gnsQuotient →ₗ[ℂ] H. -/
noncomputable def gnsIntertwinerQuotientLinearMap
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsQuotient →ₗ[ℂ] H where
  toFun := gnsIntertwinerQuotientFun φ π ξ hξ_state
  map_add' := gnsIntertwinerQuotient_add φ π ξ hξ_state
  map_smul' := gnsIntertwinerQuotient_smul φ π ξ hξ_state
```

---

### Step 3: LinearIsometry on quotient (~40 LOC)
**File:** `Main/Uniqueness.lean` (append)
**Beads ID:** `af-tests-rb9`

```lean
/-- U₀ as a linear isometry gnsQuotient →ₗᵢ[ℂ] H. -/
noncomputable def gnsIntertwinerQuotientLinearIsometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsQuotient →ₗᵢ[ℂ] H where
  toLinearMap := gnsIntertwinerQuotientLinearMap φ π ξ hξ_state
  norm_map' := gnsIntertwinerQuotient_isometry φ π ξ hξ_state

/-- The linear isometry is continuous. -/
theorem gnsIntertwinerQuotientLinearIsometry_continuous
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Continuous (gnsIntertwinerQuotientLinearIsometry φ π ξ hξ_state)
```

---

### Step 4: Extension to Hilbert space (~50 LOC)
**File:** `Main/UniquenessExtension.lean` (new file)
**Beads ID:** `af-tests-hqt`

```lean
/-- Extend U₀ to the full Hilbert space H_φ via completion. -/
noncomputable def gnsIntertwiner
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsHilbertSpace →L[ℂ] H :=
  -- Use UniformSpace.Completion.extension with the isometry

/-- The extension agrees with U₀ on embedded quotient elements. -/
theorem gnsIntertwiner_coe
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsQuotient) :
    gnsIntertwiner φ π ξ hξ_state x = gnsIntertwinerQuotientFun φ π ξ hξ_state x
```

**Key mathlib lemma:** `Isometry.completion_extension`

---

### Step 5: Extension is isometry (~35 LOC)
**File:** `Main/UniquenessExtension.lean` (append)
**Beads ID:** `af-tests-ywt`

```lean
/-- The extension preserves norms: ‖U(x)‖ = ‖x‖. -/
theorem gnsIntertwiner_norm
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsHilbertSpace) :
    ‖gnsIntertwiner φ π ξ hξ_state x‖ = ‖x‖

/-- The extension as a LinearIsometry. -/
noncomputable def gnsIntertwinerLinearIsometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsHilbertSpace →ₗᵢ[ℂ] H
```

---

### Step 6: Dense range (~40 LOC)
**File:** `Main/UniquenessExtension.lean` (append)
**Beads ID:** `af-tests-5nd`

```lean
/-- The range of U contains the dense set {π(a)ξ : a ∈ A}. -/
theorem gnsIntertwiner_range_contains_orbit
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) (a : A) :
    π a ξ ∈ Set.range (gnsIntertwiner φ π ξ hξ_state)

/-- The range of U is dense in H (using cyclicity of ξ). -/
theorem gnsIntertwiner_denseRange
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    DenseRange (gnsIntertwiner φ π ξ hξ_state)
```

---

### Step 7: Surjectivity (~40 LOC)
**File:** `Main/UniquenessExtension.lean` (append)
**Beads ID:** `af-tests-usd`

```lean
/-- An isometry with dense range into a complete space is surjective.
    This is a general fact we need to prove or find in mathlib. -/
theorem Isometry.surjective_of_denseRange_completeSpace
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {f : X → Y} (hf : Isometry f) (hd : DenseRange f) :
    Function.Surjective f

/-- The intertwiner U is surjective. -/
theorem gnsIntertwiner_surjective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    Function.Surjective (gnsIntertwiner φ π ξ hξ_state)
```

---

### Step 8: LinearIsometryEquiv (~45 LOC)
**File:** `Main/UniquenessEquiv.lean` (new file)
**Beads ID:** `af-tests-7hr`

```lean
/-- The intertwiner U is injective (isometries are injective). -/
theorem gnsIntertwiner_injective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Function.Injective (gnsIntertwiner φ π ξ hξ_state)

/-- The intertwiner U is bijective. -/
theorem gnsIntertwiner_bijective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    Function.Bijective (gnsIntertwiner φ π ξ hξ_state)

/-- The intertwiner as a LinearIsometryEquiv H_φ ≃ₗᵢ[ℂ] H. -/
noncomputable def gnsIntertwinerEquiv
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H
```

---

### Step 9: Cyclic vector mapping (~30 LOC)
**File:** `Main/UniquenessEquiv.lean` (append)
**Beads ID:** `af-tests-7em`

```lean
/-- The intertwiner sends Ω_φ to ξ. -/
theorem gnsIntertwinerEquiv_cyclic
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic φ.gnsCyclicVector = ξ
```

---

### Step 10: Intertwining on quotient (~45 LOC)
**File:** `Main/UniquenessIntertwine.lean` (new file)
**Beads ID:** `af-tests-2dx`

```lean
/-- On quotient elements: U(π_φ(a)[b]) = π(a)(U[b]).
    This is: U([ab]) = π(a)(π(b)ξ) = π(ab)ξ. -/
theorem gnsIntertwiner_intertwines_quotient
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (a : A) (x : φ.gnsQuotient) :
    gnsIntertwiner φ π ξ hξ_state (φ.gnsPreRep a x : φ.gnsHilbertSpace) =
    π a (gnsIntertwiner φ π ξ hξ_state (x : φ.gnsHilbertSpace))
```

---

### Step 11: Full intertwining property (~50 LOC)
**File:** `Main/UniquenessIntertwine.lean` (append)
**Beads ID:** `af-tests-5xr`

```lean
/-- The intertwining property: U ∘ π_φ(a) = π(a) ∘ U.
    Extended to all of H_φ by density and continuity. -/
theorem gnsIntertwiner_intertwines
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (a : A) (x : φ.gnsHilbertSpace) :
    gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic (φ.gnsRep a x) =
    π a (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic x)

/-- Alternative formulation with ContinuousLinearMap composition. -/
theorem gnsIntertwinerEquiv_comp_gnsRep
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (a : A) :
    (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic).toContinuousLinearMap ∘L φ.gnsRep a =
    π a ∘L (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic).toContinuousLinearMap
```

---

### Step 12: Final uniqueness theorem (~35 LOC)
**File:** `Main/UniquenessTheorem.lean` (new file)
**Beads ID:** `af-tests-4f9`

```lean
/-- **GNS Uniqueness Theorem**: The GNS representation is unique up to unitary equivalence.

Given any cyclic *-representation (H, π, ξ) with:
- π : A →⋆ₐ[ℂ] B(H)
- ‖ξ‖ = 1
- φ(a) = ⟨ξ, π(a)ξ⟩ for all a
- {π(a)ξ : a ∈ A} is dense in H

There exists a unitary U : H_φ ≃ₗᵢ[ℂ] H such that:
- U(Ω_φ) = ξ
- U ∘ π_φ(a) = π(a) ∘ U for all a ∈ A -/
theorem gns_uniqueness
    (hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    ∃ U : φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H,
      U φ.gnsCyclicVector = ξ ∧
      ∀ a : A, ∀ x : φ.gnsHilbertSpace, U (φ.gnsRep a x) = π a (U x)
```

---

## Summary

| Step | Description | LOC | File | Beads ID | Dependencies |
|------|-------------|-----|------|----------|--------------|
| 1 | Linearity of U₀ | ~45 | Uniqueness.lean | `af-tests-aov` | existing |
| 2 | LinearMap structure | ~35 | Uniqueness.lean | `af-tests-6tj` | Step 1 |
| 3 | LinearIsometry on quotient | ~40 | Uniqueness.lean | `af-tests-rb9` | Step 2 |
| 4 | Extension to Hilbert space | ~50 | UniquenessExtension.lean | `af-tests-hqt` | Step 3 |
| 5 | Extension is isometry | ~35 | UniquenessExtension.lean | `af-tests-ywt` | Step 4 |
| 6 | Dense range | ~40 | UniquenessExtension.lean | `af-tests-5nd` | Step 5 |
| 7 | Surjectivity | ~40 | UniquenessExtension.lean | `af-tests-usd` | Step 6 |
| 8 | LinearIsometryEquiv | ~45 | UniquenessEquiv.lean | `af-tests-7hr` | Step 7 |
| 9 | Cyclic vector mapping | ~30 | UniquenessEquiv.lean | `af-tests-7em` | Step 8 |
| 10 | Intertwining on quotient | ~45 | UniquenessIntertwine.lean | `af-tests-2dx` | Step 8 |
| 11 | Full intertwining | ~50 | UniquenessIntertwine.lean | `af-tests-5xr` | Step 10 |
| 12 | Final theorem | ~35 | UniquenessTheorem.lean | `af-tests-4f9` | Steps 9, 11 |

**Total estimated:** ~490 LOC across 5 files

## Key Mathlib Lemmas to Use

- `Isometry.completion_extension` - extend isometry to completion
- `UniformSpace.Completion.extension` - general extension to completion
- `DenseRange.mono` - subset of dense range is dense
- `LinearIsometry.isometry` - extract Isometry from LinearIsometry
- `LinearIsometryEquiv.ofBijective` or construct directly

## File Structure After Completion

```
Main/
├── VectorState.lean        # φ(a) = ⟨Ω, π(a)Ω⟩ (existing, proven)
├── Uniqueness.lean         # Steps 1-3: quotient-level intertwiner
├── UniquenessExtension.lean # Steps 4-7: extension + surjectivity
├── UniquenessEquiv.lean    # Steps 8-9: LinearIsometryEquiv
├── UniquenessIntertwine.lean # Steps 10-11: intertwining property
├── UniquenessTheorem.lean  # Step 12: final theorem
└── Theorem.lean            # Main GNS theorem (existing, proven)
```
