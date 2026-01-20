# Handoff: 2026-01-20 (Session 32)

## Completed This Session

### sq_fixes_tailA Sorry Eliminated ✓
- Created `TailAFixing.lean` with helper lemmas for tailA fixing
- Created `TailALast.lean` with 2-cycle proof for last tailA element
- Completed structural proof of `sq_fixes_tailA` in `TailLemmas.lean`

### Key Lemmas Added
- `g₂_fixes_tailA`, `g₂_inv_fixes_tailA`: g₂ fixes tailA elements
- `g₁_maps_tailA`: g₁ maps tailA to tailA or to 0 (last wraps)
- `g₁_inv_0_eq_last`: g₁⁻¹(0) = 5+n
- `c₁₃_inv_fixes_tailA`: c₁₃⁻¹ fixes ALL tailA elements
- `c₁₂_fixes_tailA_not_last`: c₁₂ fixes tailA except last (x.val < 5+n)
- `product_last_tailA_eq_4`: (c₁₂*c₁₃⁻¹)(5+n) = 4
- `product_4_eq_last_tailA`: (c₁₂*c₁₃⁻¹)(4) = 5+n
- `sq_fixes_last_tailA`: 2-cycle elimination for last tailA

---

## Current State

### Build Status: PASSING ✓

### Sorry Count: 7 total
| Location | Description | Difficulty |
|----------|-------------|------------|
| ThreeCycleProof.lean:121 | 6 core element cases | ⭐⭐ Medium |
| ThreeCycleSymmetric.lean:54 | m≥1, k=0 case | ⭐⭐⭐ Hard |
| ThreeCycleSymmetric.lean:77 | k≥1 case | ⭐⭐⭐ Hard |
| Primitivity (4 sorries) | Includes known bug | N/A |

### LOC Violations (P0)
- **TailAFixing.lean**: 201 lines (limit: 200) - needs 1 line trim
- **TailLemmas.lean**: 206 lines (limit: 200) - needs refactor

---

## 🎯 RECOMMENDED NEXT TARGET: ThreeCycleProof.lean:121

### Why This Sorry?
1. **Most tractable**: 6 independent cases, each provable separately
2. **Clear specification**: Expected values computationally verified
3. **Existing infrastructure**: formPerm lemmas already available
4. **High impact**: Completes the core three-cycle proof

### Location
```lean
-- AfTests/ThreeCycle/ThreeCycleProof.lean:121
interval_cases x.val <;> sorry -- TODO: formPerm analysis
```

### What It Needs
Prove for each core element i ∈ {0,1,2,3,4,5}:
```lean
(c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨i, _⟩ = threeCycle_0_5_1 n k ⟨i, _⟩
```

### Expected Values (VERIFIED COMPUTATIONALLY)
```
| x.val | (c₁₂*c₁₃⁻¹)²(x) | threeCycle_0_5_1(x) | Action     |
|-------|-----------------|---------------------|------------|
| 0     | 5               | 5                   | 3-cycle    |
| 1     | 0               | 0                   | 3-cycle    |
| 2     | 2               | 2                   | fixed      |
| 3     | 3               | 3                   | fixed      |
| 4     | 4               | 4                   | fixed      |
| 5     | 1               | 1                   | 3-cycle    |
```

---

## 📊 ANALYTICS FIRST: Verify Before Proving

### Step 1: Computational Verification
**ALWAYS verify with #eval before writing structural proofs!**

```lean
-- Add this to a scratch file to verify:
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨0, by omega⟩  -- expect ⟨5, _⟩
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨1, by omega⟩  -- expect ⟨0, _⟩
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨2, by omega⟩  -- expect ⟨2, _⟩
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨3, by omega⟩  -- expect ⟨3, _⟩
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨4, by omega⟩  -- expect ⟨4, _⟩
#eval (c₁₂_times_c₁₃_inv 2 0 0 ^ 2) ⟨5, by omega⟩  -- expect ⟨1, _⟩

-- Also verify the threeCycle definition:
#eval threeCycle_0_5_1 2 0 ⟨0, by omega⟩  -- expect ⟨5, _⟩
#eval threeCycle_0_5_1 2 0 ⟨5, by omega⟩  -- expect ⟨1, _⟩
#eval threeCycle_0_5_1 2 0 ⟨1, by omega⟩  -- expect ⟨0, _⟩
```

### Step 2: Trace the Chain
For each element, trace the computation manually:

**Example: Element 0**
```
(c₁₂*c₁₃⁻¹)²(0) = (c₁₂*c₁₃⁻¹)((c₁₂*c₁₃⁻¹)(0))

First application (c₁₂*c₁₃⁻¹)(0):
  c₁₃⁻¹(0) = ? (trace through g₃⁻¹, g₁⁻¹, g₃, g₁)
  c₁₂(result) = ? (trace through g₂, g₁, g₂⁻¹, g₁⁻¹)

Second application...
```

### Step 3: Use /search-mathlib
Before writing custom lemmas, search for existing mathlib results:
```
/search-mathlib formPerm apply element
/search-mathlib List.formPerm_apply_getElem
/search-mathlib Perm.mul_apply
```

---

## 🔧 HELPER LEMMA STRATEGY

### Recommended Helper File Structure
Create `CoreElementProofs.lean` with:

```lean
/-!
# Core Element Proofs for 3-Cycle Extraction

Proves (c₁₂ * c₁₃⁻¹)² acts as threeCycle_0_5_1 on core elements {0,1,2,3,4,5}.
-/

namespace AfTests.CoreElementProofs

-- SECTION 1: Single application c₁₂*c₁₃⁻¹ on core elements
theorem product_0 : c₁₂_times_c₁₃_inv n k 0 ⟨0, _⟩ = ⟨1, _⟩ := ...
theorem product_1 : c₁₂_times_c₁₃_inv n k 0 ⟨1, _⟩ = ⟨5, _⟩ := ...
theorem product_2 : c₁₂_times_c₁₃_inv n k 0 ⟨2, _⟩ = ⟨3, _⟩ := ...
theorem product_3 : c₁₂_times_c₁₃_inv n k 0 ⟨3, _⟩ = ⟨2, _⟩ := ...
theorem product_4 : c₁₂_times_c₁₃_inv n k 0 ⟨4, _⟩ = ⟨5+n, _⟩ := ... -- already in TailALast!
theorem product_5 : c₁₂_times_c₁₃_inv n k 0 ⟨5, _⟩ = ⟨0, _⟩ := ...

-- SECTION 2: Squared application
theorem sq_0 : (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨0, _⟩ = ⟨5, _⟩ := ...
theorem sq_1 : (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨1, _⟩ = ⟨0, _⟩ := ...
-- etc.

-- SECTION 3: Equality with threeCycle
theorem eq_threeCycle_0 : (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨0, _⟩ = threeCycle_0_5_1 n k ⟨0, _⟩ := ...

end AfTests.CoreElementProofs
```

### Existing Helper Lemmas to Reuse

**From TailALast.lean:**
- `g₁_fixes_4` - g₁(4) = 4
- `g₁_inv_fixes_4` - g₁⁻¹(4) = 4
- `g₂_inv_0_eq_4` - g₂⁻¹(0) = 4
- `g₃_4_eq_5` - g₃(4) = 5
- `g₁_inv_5_eq_0` - g₁⁻¹(5) = 0
- `g₁_0_eq_5` - g₁(0) = 5
- `g₃_inv_5_eq_4` - g₃⁻¹(5) = 4
- `c₁₃_inv_4_eq_0` - c₁₃⁻¹(4) = 0
- `g₂_0_eq_1` - g₂(0) = 1 (when k=0)
- `g₁_fixes_g₂_0` - g₁ fixes g₂(0)

**From TailLemmas.lean:**
- `g₁_fixes_1` - g₁(1) = 1
- `g₁_inv_fixes_1` - g₁⁻¹(1) = 1

**From ThreeCycleExtractHelpers.lean:**
- `g₃_fixes_val_ge_6` - g₃ fixes x when x.val ≥ 6
- `g₃_m0_eq` - g₃ = formPerm [2,4,5,1] when m=0

### New Helper Lemmas Likely Needed

```lean
-- g₁ core element mappings
theorem g₁_0_eq_5 : g₁ n k 0 ⟨0, _⟩ = ⟨5, _⟩  -- exists in TailALast
theorem g₁_5_eq_3 : g₁ n k 0 ⟨5, _⟩ = ⟨3, _⟩
theorem g₁_3_eq_2 : g₁ n k 0 ⟨3, _⟩ = ⟨2, _⟩
theorem g₁_2_eq_6 : g₁ n k 0 ⟨2, _⟩ = ⟨6, _⟩  -- wraps to first tailA

-- g₂ core element mappings
theorem g₂_1_eq_3 : g₂ n k 0 ⟨1, _⟩ = ⟨3, _⟩
theorem g₂_3_eq_4 : g₂ n k 0 ⟨3, _⟩ = ⟨4, _⟩
theorem g₂_4_eq_0 : g₂ n k 0 ⟨4, _⟩ = ⟨0, _⟩

-- g₃ core element mappings (when m=0)
theorem g₃_2_eq_4 : g₃ n k 0 ⟨2, _⟩ = ⟨4, _⟩
theorem g₃_5_eq_1 : g₃ n k 0 ⟨5, _⟩ = ⟨1, _⟩
theorem g₃_1_eq_2 : g₃ n k 0 ⟨1, _⟩ = ⟨2, _⟩

-- Inverse mappings (derive from forward mappings)
theorem g₁_inv_5_eq_0 : (g₁ n k 0)⁻¹ ⟨5, _⟩ = ⟨0, _⟩  -- exists
theorem g₁_inv_3_eq_5 : (g₁ n k 0)⁻¹ ⟨3, _⟩ = ⟨5, _⟩
-- etc.
```

---

## 🛠️ SKILL USAGE GUIDE

### Use /build-lean Frequently
After each edit, verify compilation:
```
/build-lean
```

### Use /search-mathlib Before Custom Proofs
```
/search-mathlib List.formPerm_apply_lt_getElem
/search-mathlib Perm.inv_eq_iff_eq
/search-mathlib Fin.ext_iff
```

### Use /analyze-sorries for Overview
```
/analyze-sorries
```

### Use /fill-sorry for Guided Filling
```
/fill-sorry ThreeCycleProof.lean:121
```

### Use /check-axioms After Completion
```
/check-axioms
```

---

## 📝 PROOF PATTERN TEMPLATES

### Pattern 1: Prove g(x) = y via formPerm
```lean
theorem g₁_a_eq_b (n k : ℕ) : g₁ n k 0 ⟨a, by omega⟩ = ⟨b, by omega⟩ := by
  unfold g₁
  have hnd := g₁_list_nodup n k 0
  have hlen := g₁_cycle_length n k 0
  -- Find position of a in list
  have hpos : idx < (g₁CoreList n k 0 ++ tailAList n k 0).length := by rw [hlen]; omega
  have h_at : (g₁CoreList n k 0 ++ tailAList n k 0)[idx]'hpos = ⟨a, by omega⟩ := by
    simp only [g₁CoreList, List.cons_append, List.getElem_cons_*]
  -- Apply formPerm
  have h_fp := List.formPerm_apply_lt_getElem _ hnd idx (by rw [hlen]; omega)
  rw [h_at] at h_fp
  -- Show next element is b
  have h_next : (g₁CoreList n k 0 ++ tailAList n k 0)[idx + 1]'_ = ⟨b, by omega⟩ := by
    simp only [g₁CoreList, List.cons_append, List.getElem_cons_*]
  rw [h_next] at h_fp
  exact h_fp
```

### Pattern 2: Prove g⁻¹(y) = x from g(x) = y
```lean
theorem g₁_inv_b_eq_a (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨b, by omega⟩ = ⟨a, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  exact (g₁_a_eq_b n k).symm
```

### Pattern 3: Prove commutator action via chaining
```lean
theorem c₁₂_x_eq_y (n k : ℕ) : commutator_g₁_g₂ n k 0 ⟨x, _⟩ = ⟨y, _⟩ := by
  unfold commutator_g₁_g₂
  simp only [Perm.mul_apply]
  -- Chain: g₂(x) → g₁(result) → g₂⁻¹(result) → g₁⁻¹(result)
  rw [g₂_x_eq_a, g₁_a_eq_b, g₂_inv_b_eq_c, g₁_inv_c_eq_y]
```

### Pattern 4: Prove squared action
```lean
theorem sq_x_eq_z (n k : ℕ) : (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨x, _⟩ = ⟨z, _⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_x_eq_y, product_y_eq_z]  -- Uses single-application lemmas
```

---

## ⚠️ COMMON PITFALLS

### 1. Import Cycles
- TailALast CANNOT import TailLemmas (would create cycle)
- Check imports before adding new dependencies

### 2. List Index Bounds
- Always provide explicit bounds proofs: `[i]'hpos`
- Use `rw [hlen]; omega` pattern for bounds

### 3. Modular Arithmetic
- `omega` doesn't understand `%` well
- Use `Nat.mod_eq_of_lt`, `Nat.mod_self` explicitly

### 4. Fin.ext vs Direct Equality
- Use `Fin.ext_iff` when omega needs to see values
- Use `Fin.ext` when constructing equality from value equality

### 5. formPerm Direction
- `List.formPerm_apply_lt_getElem`: element at i maps to element at i+1
- `List.formPerm_apply_getElem`: last element wraps to first (uses mod)

---

## 📋 CHECKLIST FOR NEXT SESSION

- [ ] Run `/analyze-sorries` to confirm current state
- [ ] Verify core element actions with `#eval` before proving
- [ ] Create `CoreElementProofs.lean` if needed (stay under 200 LOC!)
- [ ] Prove single-application lemmas first (product_0, product_1, etc.)
- [ ] Prove squared-application lemmas (sq_0, sq_1, etc.)
- [ ] Fill in `interval_cases x.val <;> sorry` with case proofs
- [ ] Run `/build-lean` after each change
- [ ] Run `/check-axioms` when complete
- [ ] Update this HANDOFF.md
- [ ] Commit with `Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>`

---

## Generator Cycle Reference

```
g₁ = formPerm [0, 5, 3, 2, 6, 7, ..., 5+n]     -- core + tailA
g₂ = formPerm [1, 3, 4, 0, 6+n, ..., 5+n+k]   -- core + tailB
g₃ = formPerm [2, 4, 5, 1]                     -- core only (when m=0)

Cycle mappings (read left-to-right):
g₁: 0→5→3→2→6→...→(5+n)→0
g₂: 1→3→4→0→(6+n)→...→(5+n+k)→1
g₃: 2→4→5→1→2
```

---

## DO NOT ❌
- Use `native_decide` for general n, k, m (only for specific values)
- Add files without checking LOC limit (200 lines max)
- Leave debugging code or verbose comments
- Create import cycles between files
- Trust handoff blindly - verify with `#eval`!

## DO ✅
- Use structural lemmas about formPerm
- Leverage existing helper lemmas (check TailALast, TailAFixing, TailLemmas)
- Factor reusable proofs into helper lemmas
- Verify cycle structures with `#eval` before writing proofs
- Use `/search-mathlib` before writing custom lemmas
- Run `/build-lean` frequently
- Keep helper files under 200 LOC
