# Handoff: 2026-01-20 (Session 30) - PHASE 3 ANALYTICAL PROOF PLAN

## CRITICAL: Do NOT Use Computational Case Analysis

The previous agent wasted time with `native_decide` case-by-case verification. **This is wrong.** The proofs must be **analytical/structural** to work for all n, k, m.

## 5 Sorries Requiring Analytical Proofs

### Files with Sorries
1. `AfTests/ThreeCycle/ThreeCycleProof.lean` - 3 sorries (lines 121, 128, 165)
2. `AfTests/ThreeCycle/ThreeCycleSymmetric.lean` - 2 sorries (lines 54, 77)

---

## PROOF PLAN FOR ThreeCycleProof.lean

### Goal: Prove `sq_isThreeCycle_n_ge1_m0` for all n ≥ 1, k, when m = 0

**Key Mathematical Insight:**
When m = 0, g₃ = formPerm([2, 4, 5, 1]) has NO tail. Therefore:
- g₃ fixes ALL elements with index ≥ 6
- The commutator c₁₃ = [g₁, g₃] has **restricted interaction** with tails

### Step 1: Prove `c₁₃_fixes_ge6` (NEW LEMMA NEEDED)

```lean
/-- When m = 0, the commutator [g₁, g₃] fixes all elements ≥ 6.
    Key insight: g₃ fixes all elements ≥ 6, so the commutator structure
    ensures tail elements return to themselves. -/
lemma c₁₃_fixes_ge6 (n k : ℕ) (x : Omega n k 0) (hx : x.val ≥ 6) :
    commutator_g₁_g₃ n k 0 x = x
```

**Proof Strategy:**
- Unfold commutator: `c₁₃(x) = g₁⁻¹(g₃⁻¹(g₁(g₃(x))))`
- Since g₃ fixes x (by `g₃_fixes_val_ge_6`): `c₁₃(x) = g₁⁻¹(g₃⁻¹(g₁(x)))`
- Case split on whether `g₁(x).val ≥ 6` or `g₁(x).val < 6`:
  - If `g₁(x).val ≥ 6`: g₃⁻¹ fixes it, so `c₁₃(x) = g₁⁻¹(g₁(x)) = x` ✓
  - If `g₁(x).val < 6`: x must be the last element of tailA (index 5+n), and g₁(x) = 0
    - Need: `g₃⁻¹(0) = 0` (since 0 ∉ [2,4,5,1])
    - Then `g₁⁻¹(0) = 5+n = x.val` ✓

**Key helper lemma needed:**
```lean
lemma zero_not_in_g₃_support (n k : ℕ) : g₃ n k 0 ⟨0, by omega⟩ = ⟨0, by omega⟩
```
Proof: 0 is not in g₃CoreList = [2, 4, 5, 1], so `formPerm_apply_of_notMem` applies.

### Step 2: Prove `sq_fixes_tailA` and `sq_fixes_tailB`

Once `c₁₃_fixes_ge6` is proven, the tail-fixing lemmas follow:

```lean
theorem sq_fixes_tailA (n k : ℕ) (hn : n ≥ 1) (x : Omega n k 0)
    (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) x = x
```

**Proof Strategy:**
- `c₁₂_times_c₁₃_inv = c₁₂ * c₁₃⁻¹`
- Since `c₁₃⁻¹` fixes x (by `c₁₃_fixes_ge6` + inverse), we have:
  `(c₁₂ * c₁₃⁻¹)(x) = c₁₂(x)`
- Show `c₁₂` maps tail elements in 2-cycles: analyze g₁, g₂ cycle structure
- Squaring a 2-cycle gives identity

**Alternative approach:** Show that for x ≥ 6:
- The permutation `c₁₂_times_c₁₃_inv` restricted to {elements ≥ 6} has order dividing 2
- Therefore squaring gives identity on this set

### Step 3: Prove Core Element Actions (line 165)

The `interval_cases x.val <;> sorry` needs 6 proofs for x.val ∈ {0,1,2,3,4,5}.

**Key Insight:** Core action is determined by formPerm structure on core lists.

For each core element i, prove:
```lean
(c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨i, _⟩ = threeCycle_0_5_1 n k ⟨i, _⟩
```

**Proof Strategy for each case:**
- Unfold all definitions (c₁₂, c₁₃, generators)
- Use `List.formPerm_apply_mem` for elements in the list
- Use `List.formPerm_apply_of_notMem` for elements not in the list
- The core action depends ONLY on core lists (not tails) because:
  - Elements {0,1,2,3,4,5} are in core positions of generator lists
  - Their images under formPerm are determined by adjacent elements in the list
  - The adjacent elements are also core elements (or wrap to core)

**Specific values to prove:**
| x.val | (c₁₂*c₁₃⁻¹)²(x) | threeCycle(x) | Equality |
|-------|-----------------|---------------|----------|
| 0     | 5               | 5             | ✓        |
| 1     | 0               | 0             | ✓        |
| 2     | 2               | 2             | ✓        |
| 3     | 3               | 3             | ✓        |
| 4     | 4               | 4             | ✓        |
| 5     | 1               | 1             | ✓        |

Use `Fin.ext_iff` and explicit computation with formPerm lemmas.

---

## PROOF PLAN FOR ThreeCycleSymmetric.lean

### Sorry 1: `isThreeCycle_m_ge1_k0` (line 54)

```lean
theorem isThreeCycle_m_ge1_k0 (n m : ℕ) (hm : m ≥ 1) :
    ((commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹) ^ 2).IsThreeCycle
```

**This is symmetric to the n≥1, m=0 case:**
- When k = 0, g₂ has no tail B
- g₂ fixes all elements ≥ 6+n
- Apply the same structural argument with roles swapped

### Sorry 2: `isThreeCycle_k_ge1` (line 77)

```lean
theorem isThreeCycle_k_ge1 (n k m : ℕ) (hk : k ≥ 1) :
    ((iteratedComm_g₂' n k m) ^ 2).IsThreeCycle
```

**Different construction:** Uses iterated commutator `[[g₁,g₂], g₂]`
- Analyze the nested commutator structure
- Show it has cycle type {3, 2, ...}
- Squaring gives {3}

---

## KEY MATHLIB LEMMAS TO USE

```lean
-- formPerm behavior
List.formPerm_apply_mem_of_nodup : x ∈ l → l.formPerm x = next element
List.formPerm_apply_of_notMem : x ∉ l → l.formPerm x = x
List.formPerm_symm : (l.formPerm)⁻¹ = l.reverse.formPerm

-- Permutation composition
Perm.mul_apply : (σ * τ) x = σ (τ x)
Perm.inv_apply_self : σ⁻¹ (σ x) = x

-- Support characterization
Perm.mem_support : x ∈ σ.support ↔ σ x ≠ x
card_support_eq_three_iff : σ.support.card = 3 ↔ σ.IsThreeCycle
```

---

## FILE STRUCTURE

```
AfTests/ThreeCycle/
├── ThreeCycleExtractHelpers.lean  -- Add c₁₃_fixes_ge6 here (≤200 LOC!)
├── ThreeCycleProof.lean           -- Fix 3 sorries
└── ThreeCycleSymmetric.lean       -- Fix 2 sorries
```

**WARNING:** ThreeCycleExtractHelpers.lean is at 200 lines. May need to create a new file for additional lemmas.

---

## VERIFICATION COMMANDS

```bash
# After fixing each sorry, verify:
lake build AfTests.ThreeCycle.ThreeCycleProof
lake build AfTests.ThreeCycle.ThreeCycleSymmetric
lake build AfTests.MainTheorem

# Check no sorries remain:
grep -rn "sorry" AfTests/ThreeCycle/ --include="*.lean"
```

---

## DO NOT

- ❌ Use `native_decide` for general n, k, m
- ❌ Use computational case-by-case verification
- ❌ Add more match cases
- ❌ Leave sorries with "TODO" comments

## DO

- ✅ Prove structural lemmas about formPerm behavior
- ✅ Use mathlib's permutation infrastructure
- ✅ Prove properties for ALL parameter values analytically
- ✅ Factor out reusable lemmas
