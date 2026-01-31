# Handoff: 2026-01-31 (Session 64)

## Completed This Session

### 1. Peirce Decomposition Theorem (af-bqjd) - MAJOR PROGRESS ✅
- **File:** `AfTests/Jordan/Peirce.lean:441-661`
- **New theorems added:**
  - `peirceProj₀`, `peirceProj₁₂`, `peirceProj₁` — Lagrange interpolation projections
  - `peirceProj_sum` — Three projections sum to identity ✅
  - `peirceProj₀_mem`, `peirceProj₁₂_mem`, `peirceProj₁_mem` — Projections map into correct spaces ✅
  - `peirce_decomposition` — Every element decomposes as x₀ + x_{1/2} + x₁ ✅
  - `peirceSpace_iSup_eq_top` — Peirce spaces span the algebra ✅
  - `peirce_direct_sum` — Internal direct sum (1 sorry remaining for independence)

### Key Technique: Lagrange Interpolation Projections
The Peirce polynomial `L_e(L_e - 1/2)(L_e - 1) = 0` has roots at 0, 1/2, 1.
Using Lagrange interpolation, we construct:
```
π₀ = 2(L - 1/2)(L - 1) = 2L² - 3L + 1
π_{1/2} = -4L(L - 1) = -4L² + 4L
π₁ = 2L(L - 1/2) = 2L² - L
```
These satisfy π₀ + π_{1/2} + π₁ = id and each maps into its Peirce space.

---

## Current State

| Metric | Value |
|--------|-------|
| Total LOC | ~25,000 |
| Total Sorries | 19 (+1 from direct sum independence) |
| Issues Closed | 292 / 316 (92%) |

### Component Health
| Component | LOC | Sorries | Status |
|-----------|-----|---------|--------|
| GNS/ | 2,455 | 0 | Complete |
| ArchimedeanClosure/ | 4,943 | 0 | Complete |
| Jordan/ | ~5,050 | 19 | Active |

---

## 🎯 NEXT SESSION: Complete peirce_direct_sum Independence

### Remaining Work on af-bqjd
The `peirce_direct_sum` theorem needs the `iSupIndep` (independence) proof:
- Show P₀ ∩ (P_{1/2} ⊔ P₁) = {0}
- Show P_{1/2} ∩ (P₀ ⊔ P₁) = {0}
- Show P₁ ∩ (P₀ ⊔ P_{1/2}) = {0}

**Strategy:** For each case, if x ∈ P_λ and x = y + z with y, z in other spaces:
- Apply L_e to get eigenvalue equations
- Solve system to show y = z = 0, hence x = 0

### Spectral Theory Dependency Chain

```
af-dxb5 (P0/P1 rules) ← COMPLETE ✅
    └── af-qvqz (P1/2 rules) ← COMPLETE ✅
            └── af-bqjd (Peirce decomposition) ← 90% COMPLETE (1 sorry)
                    └── af-nnvl (Eigenspace definition)
                            └── af-9pfg (Eigenspace orthogonality)
                                    └── af-pyaw (Spectral theorem) [P1]
```

---

## Proof Techniques Discovered (New This Session)

### Lagrange Interpolation for Projections
For minimal polynomial p(x) = x(x - 1/2)(x - 1), the projection onto eigenspace λ is:
```
π_λ = ∏_{μ≠λ} (L - μ) / (λ - μ)
```
This gives explicit formulas that can be verified algebraically.

### smul_jmul vs jmul_smul
- `smul_jmul r a b : jmul a (r • b) = r • jmul a b` — pulls scalar from second argument
- `jmul_smul r a b : jmul (r • a) b = r • jmul a b` — pulls scalar from first argument

---

## Known Gotchas

| Issue | Solution |
|-------|----------|
| ℕ-smul vs ℝ-smul | `simp only [← Nat.cast_smul_eq_nsmul ℝ]` |
| `linarith` on modules | Use `abel`, `module`, or `calc` chains |
| Negative smul | `(-4) • x` is canonical, not `-(4 • x)` |
| Submodule iSup | Use `le_iSup f i` explicitly with the function |
| smul_sub distribution | `rw [smul_sub, smul_smul]` then `norm_num` |

---

## Files Modified This Session

- `AfTests/Jordan/Peirce.lean` — Peirce decomposition theorem (~220 new LOC)
- `HANDOFF.md` — This file
