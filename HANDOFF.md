# Handoff: 2026-01-20 (Session 29) - PHASE 3 SORRY ELIMINATION

## CRITICAL: 5 Sorries Block Complete Main Theorem Proof

The main theorem structure is complete but 5 sorries MUST be eliminated.

## IMMEDIATE ACTION REQUIRED

### Sorry 1: ThreeCycleProof.lean:120 - sq_fixes_tailA

```lean
theorem sq_fixes_tailA (n k : ℕ) (hn : n ≥ 1) (x : Omega n k 0)
    (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) x = x
```

**PROOF STRATEGY:**
1. First prove c₁₃ fixes all tail elements when m=0:
   ```lean
   lemma c₁₃_fixes_tail_m0 (n k : ℕ) (x : Omega n k 0) (hx : x.val ≥ 6) :
       commutator_g₁_g₃ n k 0 x = x
   ```

   Proof outline:
   - g₃(x) = x (use g₃_fixes_val_ge_6 from ThreeCycleExtractHelpers)
   - g₁(g₃(x)) = g₁(x)
   - g₃⁻¹(g₁(x)) = g₁(x) when g₁(x).val ≥ 6, OR = g₁(x) when g₁(x) = 0 (since 0 ∉ g₃CoreList)
   - g₁⁻¹(g₁(x)) = x

   Key lemma needed: `0 ∉ g₃CoreList` (g₃CoreList = [2,4,5,1], so 0 is fixed by g₃)

2. Since c₁₃⁻¹ also fixes tails, c₁₂ * c₁₃⁻¹ has same tail action as c₁₂

3. Show c₁₂ acts on tail A as 2-cycles that square to identity

**FILE TO EDIT:** AfTests/ThreeCycle/ThreeCycleExtractHelpers.lean - add c₁₃_fixes_tail_m0

### Sorry 2: ThreeCycleProof.lean:127 - sq_fixes_tailB

Same strategy as Sorry 1. Tail B elements are NOT in g₁ or g₃ support when m=0.

### Sorry 3: ThreeCycleProof.lean:164 - Core element actions

```lean
interval_cases x.val <;> sorry -- needs 6 proofs for x.val ∈ {0,1,2,3,4,5}
```

**PROOF STRATEGY:**
For each x.val ∈ {0,1,2,3,4,5}, prove:
```lean
(c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨i, _⟩ = ThreeCycleExtract.threeCycle_0_5_1 n k ⟨i, _⟩
```

Expected values (threeCycle_0_5_1 = formPerm [0,5,1]):
- x.val=0: both sides = ⟨5, _⟩
- x.val=1: both sides = ⟨0, _⟩
- x.val=5: both sides = ⟨1, _⟩
- x.val=2,3,4: both sides = x (fixed)

**APPROACH:** Prove core action is independent of n,k by showing:
1. formPerm acts on list elements based only on position in list
2. Core elements {0,1,2,3,4,5} have fixed positions in generator lists
3. The commutator structure on core is determined by core positions only

Add helper lemmas to ThreeCycleExtractHelpers.lean:
```lean
-- The squared product maps 0 to 5 for all n≥1, k
lemma sq_core_action_0 (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨0, by omega⟩ = ⟨5, by omega⟩

-- Similar for 1→0, 5→1, 2→2, 3→3, 4→4
```

### Sorry 4: ThreeCycleSymmetric.lean:54 - isThreeCycle_m_ge1_k0

```lean
theorem isThreeCycle_m_ge1_k0 (n m : ℕ) (hm : m ≥ 1) :
    ((commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹) ^ 2).IsThreeCycle
```

**PROOF STRATEGY:** Symmetric to the n≥1,m=0 case.
When k=0, g₂ has no tail B, so g₂ fixes elements ≥6+n.
Apply same structural argument.

### Sorry 5: ThreeCycleSymmetric.lean:77 - isThreeCycle_k_ge1

```lean
theorem isThreeCycle_k_ge1 (n k m : ℕ) (hk : k ≥ 1) :
    ((iteratedComm_g₂' n k m) ^ 2).IsThreeCycle
```

**PROOF STRATEGY:** The iterated commutator [[g₁,g₂],g₂] has similar cycle structure.
When k≥1, the nested commutator produces cycle type {3,2,...}, squaring gives {3}.

## EXPLICIT COMMANDS TO RUN

```bash
# 1. Open the main file to edit
code AfTests/ThreeCycle/ThreeCycleExtractHelpers.lean

# 2. Add lemma proving 0 is not in g₃'s support
# After line 75 (after g₃_fixes_tailB), add:

lemma zero_not_in_g₃CoreList (n k m : ℕ) :
    (⟨0, by omega⟩ : Omega n k m) ∉ g₃CoreList n k m := by
  simp only [g₃CoreList, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [Fin.mk.injEq]; omega

# 3. Add lemma proving c₁₃ fixes tail elements when m=0
lemma c₁₃_fixes_ge6_m0 (n k : ℕ) (x : Omega n k 0) (hx : x.val ≥ 6) :
    commutator_g₁_g₃ n k 0 x = x := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply, Perm.inv_apply_self]
  -- g₃(x) = x since m=0 and x.val ≥ 6
  have hg₃ : g₃ n k 0 x = x := g₃_fixes_val_ge_6 n k x hx
  rw [hg₃]
  -- Need: g₁⁻¹(g₃⁻¹(g₁(x))) = x
  -- Case split on whether g₁(x).val ≥ 6
  by_cases h : (g₁ n k 0 x).val ≥ 6
  · -- g₁(x) is also a tail element, g₃ fixes it
    have hg₃' : g₃ n k 0 (g₁ n k 0 x) = g₁ n k 0 x := g₃_fixes_val_ge_6 n k _ h
    simp only [hg₃', Perm.inv_apply_self]
  · -- g₁(x) is a core element (must be 0 since x is last in tailA)
    push_neg at h
    -- 0 is not in g₃'s support, so g₃⁻¹(g₁(x)) = g₁(x)
    sorry -- Complete this case

# 4. Build and test
lake build AfTests.ThreeCycle.ThreeCycleExtractHelpers

# 5. Then update ThreeCycleProof.lean to use the new lemma
```

## KEY MATHLIB LEMMAS TO USE

```lean
-- formPerm fixes elements not in list
List.formPerm_apply_of_notMem : x ∉ l → l.formPerm x = x

-- Inverse of formPerm
List.formPerm_symm_apply_of_notMem

-- Support of formPerm
List.support_formPerm_of_nodup
```

## FILE LOCATIONS

- ThreeCycleExtractHelpers.lean: `/home/tobias/Projects/af-tests/AfTests/ThreeCycle/ThreeCycleExtractHelpers.lean`
- ThreeCycleProof.lean: `/home/tobias/Projects/af-tests/AfTests/ThreeCycle/ThreeCycleProof.lean`
- ThreeCycleSymmetric.lean: `/home/tobias/Projects/af-tests/AfTests/ThreeCycle/ThreeCycleSymmetric.lean`
- Generator definitions: `/home/tobias/Projects/af-tests/AfTests/Core/Generators.lean`

## VERIFICATION

After eliminating sorries, run:
```bash
lake build AfTests.MainTheorem
grep -rn "sorry" AfTests/ --include="*.lean"  # Should show only Lemma11_5 sorries
```

## DO NOT

- Do not just document the sorries
- Do not say "this is Phase 2 work"
- Do not leave sorries with comments "TODO"
- ACTUALLY WRITE THE PROOFS
