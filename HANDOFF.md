# Handoff: 2026-01-19 (Session 16)

## Completed This Session

### Lemma11_4.lean - Block Orbit Divisibility
1. **Restructured proof strategy** for `block_orbit_divides_cycle_length`
   - Added import `Mathlib.GroupTheory.GroupAction.Period`
   - Opened `scoped Pointwise` for set action `σ • B = σ '' B`
   - Introduced helper lemmas:
     - `perm_smul_set_eq_image`: Shows `σ • B = σ '' B` via pointwise action
     - `blockOrbit_eq_orbit`: Connects blockOrbit to MulAction orbit
     - `setPeriod`: Wrapper for `MulAction.period σ B`
     - `setPeriod_dvd_orderOf`: Period divides orderOf (from mathlib)

2. **Proof structure established** for main theorem:
   ```lean
   block_orbit_divides_cycle_length :=
     blockOrbitSize = setPeriod  -- (SORRY: line 127)
     → setPeriod ∣ orderOf σ     -- (mathlib: period_dvd_orderOf)
     → orderOf σ = cycleLength   -- (mathlib: IsCycle.orderOf)
   ```

3. **Key insight documented**: The orbit size equals the period because:
   - Orbit = { σ^k • B | k ∈ ℤ } = { σ^k • B | k ∈ {0,...,p-1} } where p = period
   - These p elements are distinct (by definition of period)
   - Use `periodicOrbit_length` from `Mathlib.Dynamics.PeriodicPts.Defs`

## Current State

- **Build status**: PASSING (with sorries)
- **Sorry count**: 11 total
- **Open P0 blockers**: None

## Remaining Sorries in Lemma11_4.lean (3)

| Line | Lemma | Strategy |
|------|-------|----------|
| 127 | `blockOrbitSize_eq_setPeriod` | Show ncard of orbit = minimalPeriod using `periodicOrbit_length` and `period_eq_minimalPeriod` |
| 165 | `orbit_blocks_partition_support` | Show orbit blocks cover supp(σ) using cycle transitivity |
| 177 | `block_support_intersection_card` | Counting: ℓ elements / r blocks = ℓ/r per block |

## Key Mathlib Lemmas Identified

```lean
-- From Mathlib.GroupTheory.GroupAction.Period
period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m
period_eq_minimalPeriod : period m a = minimalPeriod (m • ·) a

-- From Mathlib.Dynamics.PeriodicPts.Defs
periodicOrbit_length : (periodicOrbit f x).length = minimalPeriod f x
nodup_periodicOrbit : (periodicOrbit f x).Nodup
mem_periodicOrbit_iff (hx) : y ∈ periodicOrbit f x ↔ ∃ n, f^[n] x = y

-- From Mathlib.GroupTheory.Perm.Cycle.Basic
IsCycle.orderOf : orderOf σ = σ.support.card
```

## Next Steps (Priority Order)

1. **Complete `blockOrbitSize_eq_setPeriod`** (line 127)
   - Use `period_eq_minimalPeriod` to connect MulAction.period to minimalPeriod
   - Use `periodicOrbit_length` and show blockOrbit equals periodicOrbit's underlying set
   - Key: `ncard {σ^k • B | k} = length (periodicOrbit (σ • ·) B) = minimalPeriod = period`

2. **Complete `orbit_blocks_partition_support`** (line 165)
   - Use cycle's transitivity on support
   - For any x ∈ supp(σ), exists y ∈ B ∩ supp(σ), exists k s.t. σ^k(y) = x
   - Then x ∈ σ^k(B) ∩ supp(σ)

3. **Complete `block_support_intersection_card`** (line 177)
   - Uses the partition + orbit size divides cycle length
   - Counting argument: r blocks partition ℓ elements evenly

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_4.lean` - Major restructuring with Period-based approach

## Known Issues / Gotchas

- **Pointwise scope required**: Must use `open scoped Pointwise` for `σ • B` notation on sets
- **Period vs minimalPeriod**: `MulAction.period` = `Function.minimalPeriod` (see `period_eq_minimalPeriod`)
- **zpow vs pow orbit**: Integer zpowers give same orbit as nat powers for finite types
- **LOC Status**: Lemma11_4.lean is ~195 lines (under 200 limit)

## Issue Status

- **af-tests-2hl** (Lemma11_4): IN_PROGRESS - reduced from 6 to 3 sorries, proof strategy established
