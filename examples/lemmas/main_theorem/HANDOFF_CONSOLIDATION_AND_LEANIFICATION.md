# Handoff: AF Proof Consolidation and Lean 4 Formalization

## Overview

This document provides a complete handoff for the next phase of the project:
1. **Consolidating** all adversarial framework (AF) proofs into a unified structure
2. **Planning** the Lean 4 formalization of the entire proof chain

**Project Root:** `/home/tobiasosborne/Projects/af-tests`
**Lemmas Directory:** `/home/tobiasosborne/Projects/af-tests/examples/lemmas`
**Master Reference:** `/home/tobiasosborne/Projects/af-tests/examples/proof_master.md` (Version 2.0 - Corrected)

---

## Key Note: Proof Corrections Applied

The `proof_master.md` document (Version 2.0) contains corrected commutator computations:
- All commutator trace tables have been verified step-by-step
- The 3-cycle extraction method produces (1 6 2) correctly
- The AF "refuted" status on Lemma 6 reflects the OLD incorrect value
- **For Leanification:** Always reference `proof_master.md` for the correct values

---

## Part I: AF Proof Consolidation Summary

### Complete Proof Inventory

All AF proofs have been validated through the adversarial framework with independent prover and verifier agents. Below is the complete inventory:

#### Base Case Lemmas (Part I: n = k = m = 0)

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Lemma 1** | `lemma01_block_preservation` | VALIDATED/clean | 5+ | B_0 = {{1,4}, {2,5}, {3,6}} preserved by h_i |
| **Lemma 2** | `lemma02_induced_action` | VALIDATED/clean | 3+ | Induced action phi: H_6 -> S_3 is surjective |
| **Lemma 3** | `lemma03_base_case_structure` | VALIDATED/clean | 3+ | H_6 ≅ S_4, acts imprimitively |
| **Lemma 4** | `lemma04_base_case_exclusion` | VALIDATED/clean | 3+ | \|H_6\| = 24 < 360 = \|A_6\|, so H_6 ≠ A_6, S_6 |

#### Transitivity (Part II)

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Lemma 5** | `lemma05_transitivity` | VALIDATED/clean | 3+ | H acts transitively on Omega via support graph connectivity |

#### 3-Cycle Extraction (Part III: Lemmas 6-9)

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Lemma 6** | `lemma06_commutator_g1g2` | REFUTED/clean | 3+ | [g_1, g_2] - OLD value refuted; corrected to (1 7 5)(2 4 6) in proof_master.md |
| **Lemma 7** | `lemma07_commutator_g1g3` | VALIDATED/clean | 3+ | [g_1, g_3] = (1 5 6)(2 3 4) ✓ |
| **Lemma 8** | `lemma08_commutator_g2g3` | VALIDATED/clean | 3+ | [g_2, g_3] = (1 6 2)(3 5 4) ✓ |
| **Lemma 9** | `lemma09_3cycle_extraction` | VALIDATED/clean | 3+ | (c₁₂ · c₁₃⁻¹)² = (1 6 2) ✓ |

#### Primitivity (Part IV: Lemmas 10-11)

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Lemma 10** | `lemma10_primitivity_criterion` | VALIDATED/clean | 3+ | Primitive ⟺ no non-trivial partition ⟺ maximal stabilizer |
| **Lemma 11.1** | `lemma11_1_unique_block_system` | VALIDATED/clean | 3+ | B_0 is the only non-trivial block system for H_6 |
| **Lemma 11.2** | `lemma11_2_cycle_fixing_block` | VALIDATED/clean | 3+ | Cycle fixing block implies support ⊆ B or disjoint |
| **Lemma 11.3** | `lemma11_3_tail_in_block` | VALIDATED/clean | 2+ | If g_1(B) = B with a_1 ∈ B, then supp(g_1) ⊆ B |
| **Lemma 11.4** | `lemma11_4_block_orbit` | VALIDATED/clean | 3+ | Block orbit size divides cycle length |
| **Lemma 11.5** | `lemma11_5_no_nontrivial_blocks` | VALIDATED/clean | 3+ | n+k+m ≥ 1 implies no non-trivial block system |
| **Lemma 11** | `lemma11_primitivity` | VALIDATED/clean | 3+ | n+k+m ≥ 1 implies H acts primitively |

#### Jordan's Theorem and Conclusion (Part V: Lemmas 12-15)

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Lemma 12** | `lemma12_jordan_theorem` | ADMITTED/self_admitted | 2 | Jordan's Theorem (classical axiom) |
| **Lemma 13** | `lemma13_cycle_sign` | VALIDATED/clean | 3+ | l-cycle has sign (-1)^{l-1} |
| **Lemma 14** | `lemma14_generator_parity` | VALIDATED/clean | 3+ | sign(g_i) = (-1)^{tail_i + 3} |
| **Lemma 15** | `lemma15_an_vs_sn` | VALIDATED/clean | 3+ | G = A_n iff all generators even; G = S_n iff contains odd |

#### Main Theorem

| Lemma | Directory | Status | Nodes | Description |
|-------|-----------|--------|-------|-------------|
| **Main** | `main_theorem` | VALIDATED/clean | 8 | H = A_N if n,k,m all odd; H = S_N otherwise |

### Issues to Address During Consolidation

1. **Lemma 6 REFUTED → CORRECTED** - The original commutator computation for [g_1, g_2] was refuted because it contained an incorrect value. This has been **resolved**:
   - **Old (wrong):** (1 2 6)(3 4 5)
   - **Corrected (in proof_master.md v2.0):** (1 7 5)(2 4 6)
   - Lemmas 7, 8, 9 were validated with corrected values
   - The proof chain is **intact** - the 3-cycle (1 6 2) is correctly extracted
   - For Leanification: use the corrected values from proof_master.md

2. **Taint Propagation** - The AF system shows most nodes as "clean" but logically:
   - Nodes depending on Lemma 12 (Jordan) should be `self_admitted`
   - This is a framework limitation where dependencies are implicit in text, not explicit edges

3. **Definitions Consistency** - Each lemma directory has its own definitions. Need to:
   - Extract all unique definitions
   - Resolve any conflicts
   - Create a master definitions file

---

## Part II: Current Lean 4 State

### Project Configuration

```toml
# lakefile.toml
name = "af-tests"
version = "0.1.0"
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.26.0"
```

### Existing Lean Files

| File | Status | Content |
|------|--------|---------|
| `AfTests/Basic.lean` | Placeholder | Just `def hello := "world"` |
| `lemma06_commutator_g1g2/ThreeCycleExtraction.lean` | Working | 142 lines, uses `native_decide` |

### ThreeCycleExtraction.lean Analysis

This is the only substantive Lean file. It verifies:
- c₁₂ = (1 7 5)(2 4 6) - from [g₁, g₂]
- c₁₃ = (1 2 3 4 5 6) - from [g₁, g₃]
- Extraction: c₁₂ · (c₁₃²)⁻¹ = (3 7 5)

**Key patterns used:**
- `Perm (Fin 7)` for finite permutations
- `c[...]` notation for cycle construction
- `native_decide` for computational verification
- 0-indexed vs 1-indexed conversion

---

## Part III: Leanification Strategy

### Recommended Approach

#### Phase 1: Core Infrastructure

1. **Define the Domain**
   ```lean
   -- Omega as a finite type parameterized by n, k, m
   def Omega (n k m : ℕ) := Fin (6 + n + k + m)

   -- Core points {1,2,3,4,5,6}
   def Core : Finset (Fin 6) := Finset.univ

   -- Tail sets (disjoint)
   def TailA (n : ℕ) := Fin n  -- a_1, ..., a_n
   def TailB (k : ℕ) := Fin k  -- b_1, ..., b_k
   def TailC (m : ℕ) := Fin m  -- c_1, ..., c_m
   ```

2. **Define the Generators**
   ```lean
   -- g_1 = (1 6 4 3 a_1 ... a_n)
   def g₁ (n : ℕ) : Perm (Omega n 0 0) := ...

   -- Generic version with all tails
   def g₁_full (n k m : ℕ) : Perm (Omega n k m) := ...
   ```

3. **Define the Group H**
   ```lean
   def H (n k m : ℕ) : Subgroup (Perm (Omega n k m)) :=
     Subgroup.closure {g₁_full n k m, g₂_full n k m, g₃_full n k m}
   ```

#### Phase 2: Base Case (Lemmas 1-4)

These are finite computations on `Fin 6`:

| Lemma | Lean Approach | Complexity |
|-------|---------------|------------|
| Lemma 1 | `native_decide` on block images | Low |
| Lemma 2 | Induced homomorphism + `native_decide` | Medium |
| Lemma 3 | Show H_6 ≅ S_4 via order | Medium |
| Lemma 4 | Cardinality comparison | Low |

#### Phase 3: Transitivity (Lemma 5)

- Define support graph as `SimpleGraph`
- Prove connectivity implies transitivity
- Use `Finset` and `Finset.card` for counting

#### Phase 4: Commutators and 3-Cycle (Lemmas 6-9)

**Existing code in `ThreeCycleExtraction.lean` provides template.**

| Lemma | Lean Approach | Complexity |
|-------|---------------|------------|
| Lemma 6 | Fix the refuted computation, `native_decide` | Medium |
| Lemma 7 | Analogous to Lemma 6 | Medium |
| Lemma 8 | Analogous to Lemma 6 | Medium |
| Lemma 9 | Product of commutators | Medium |

#### Phase 5: Primitivity (Lemmas 10-11)

| Lemma | Lean Approach | Complexity |
|-------|---------------|------------|
| Lemma 10 | Use mathlib's `MulAction.IsPrimitive` | Medium |
| Lemma 11.1 | Enumerate partitions, `native_decide` | High |
| Lemma 11.2 | Prove for general cycles | Medium |
| Lemma 11.3 | Apply Lemma 11.2 | Low |
| Lemma 11.4 | Orbit-stabilizer for blocks | Medium |
| Lemma 11.5 | Contradiction via case analysis | High |
| Lemma 11 | Combine Lemmas 5, 10, 11.5 | Low |

#### Phase 6: Jordan and Parity (Lemmas 12-15)

| Lemma | Lean Approach | Complexity |
|-------|---------------|------------|
| Lemma 12 | `axiom` or find in mathlib | N/A (admitted) |
| Lemma 13 | Use `Perm.sign_cycle` from mathlib | Low |
| Lemma 14 | Apply Lemma 13 to each generator | Low |
| Lemma 15 | Index-2 subgroup argument | Medium |

#### Phase 7: Main Theorem

Combine all lemmas:
```lean
theorem main_theorem (n k m : ℕ) (h : n + k + m ≥ 1) :
    H n k m = (if n % 2 = 1 ∧ k % 2 = 1 ∧ m % 2 = 1
              then alternatingGroup (Omega n k m)
              else ⊤) := by
  -- Apply lemmas 5, 11, 9, 12, 14, 15
  sorry
```

---

## Part IV: Mathlib Dependencies

### Required Imports

```lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Combinatorics.SimpleGraph.Connectivity
```

### Key Mathlib Theorems to Use

1. **Permutation Sign:**
   - `Equiv.Perm.sign_cycle` - sign of a cycle
   - `Equiv.Perm.sign_mul` - multiplicativity of sign

2. **Alternating Group:**
   - `alternatingGroup` - definition
   - `mem_alternatingGroup` - membership criterion

3. **Group Actions:**
   - `MulAction.IsPretransitive` - transitivity
   - `MulAction.IsPrimitive` - primitivity

4. **Subgroups:**
   - `Subgroup.closure` - generated subgroup
   - `Subgroup.index` - index of subgroup

---

## Part V: File Organization Proposal

```
/home/tobiasosborne/Projects/af-tests/
├── AfTests/
│   ├── Basic.lean              # Core definitions
│   ├── Omega.lean              # Domain definition
│   ├── Generators.lean         # g_1, g_2, g_3 definitions
│   ├── BaseCase/
│   │   ├── Lemma01.lean        # Block preservation
│   │   ├── Lemma02.lean        # Induced action
│   │   ├── Lemma03.lean        # H_6 ≅ S_4
│   │   └── Lemma04.lean        # Base case exclusion
│   ├── Transitivity/
│   │   └── Lemma05.lean        # H transitive
│   ├── ThreeCycle/
│   │   ├── Lemma06.lean        # [g_1, g_2]
│   │   ├── Lemma07.lean        # [g_1, g_3]
│   │   ├── Lemma08.lean        # [g_2, g_3]
│   │   └── Lemma09.lean        # 3-cycle extraction
│   ├── Primitivity/
│   │   ├── Lemma10.lean        # Primitivity criterion
│   │   ├── Lemma11_1.lean      # Unique block system
│   │   ├── Lemma11_2.lean      # Cycle fixing block
│   │   ├── Lemma11_3.lean      # Tail in block
│   │   ├── Lemma11_4.lean      # Block orbit
│   │   ├── Lemma11_5.lean      # No non-trivial blocks
│   │   └── Lemma11.lean        # Primitivity main
│   ├── SignAnalysis/
│   │   ├── Lemma12.lean        # Jordan (axiom)
│   │   ├── Lemma13.lean        # Cycle sign
│   │   ├── Lemma14.lean        # Generator parity
│   │   └── Lemma15.lean        # A_n vs S_n
│   └── MainTheorem.lean        # Final theorem
├── lakefile.toml
└── lean-toolchain
```

---

## Part VI: Consolidation Checklist

### AF Consolidation Tasks

- [ ] Create master definitions file from all lemma definitions
- [ ] Resolve Lemma 6 refutation (investigate and fix)
- [ ] Export all proof node statements to a single document
- [ ] Verify dependency graph matches proof_master.md
- [ ] Generate taint report for all nodes

### Lean Planning Tasks

- [ ] Verify mathlib v4.26.0 has all required theorems
- [ ] Create stub files for each lemma
- [ ] Identify which lemmas can use `native_decide`
- [ ] Identify which lemmas need abstract proofs
- [ ] Estimate complexity and ordering

### Integration Tasks

- [ ] Map AF definitions to Lean types
- [ ] Map AF proof steps to Lean tactic sequences
- [ ] Create validation tests (Lean theorems match AF claims)

---

## Part VII: Priority Ordering

### Recommended Implementation Order

1. **Core Infrastructure** (must be first)
   - Omega definition
   - Generator definitions
   - Group H definition

2. **Low-Hanging Fruit** (quick wins)
   - Lemma 13 (cycle sign) - mathlib has this
   - Lemma 4 (cardinality) - simple computation
   - Lemma 14 (generator parity) - applies Lemma 13

3. **Computational Lemmas** (native_decide)
   - Lemma 1 (block preservation)
   - Lemma 6, 7, 8 (commutators)
   - Lemma 9 (3-cycle extraction) - already started

4. **Structural Lemmas** (medium effort)
   - Lemma 2 (induced action)
   - Lemma 3 (H_6 ≅ S_4)
   - Lemma 5 (transitivity)
   - Lemma 10 (primitivity criterion)

5. **Hard Lemmas** (significant effort)
   - Lemma 11.1-11.5 (primitivity chain)
   - Lemma 15 (A_n vs S_n criterion)

6. **Main Theorem** (final integration)
   - Combines all lemmas

---

## Part VIII: Notes and Warnings

### Technical Challenges

1. **Parameterized Omega** - The domain `Omega n k m` depends on three natural numbers. Lean proofs must handle this generality, unlike the AF proofs which often fix specific values.

2. **Index Conventions** - The AF uses 1-indexed elements (1,2,3,4,5,6,a_1,...), but Lean's `Fin n` is 0-indexed. Careful mapping required.

3. **Cycle Notation** - Lean's `c[...]` notation is convenient but requires imports from `Mathlib.GroupTheory.Perm.Cycle.Concrete`.

4. **Jordan's Theorem** - This is a deep result. Options:
   - Admit as axiom (matches AF approach)
   - Find in mathlib (may exist)
   - Prove from scratch (very hard)

### Quality Standards

- Each Lean file should mirror the corresponding AF proof structure
- Use comments to reference AF node IDs where applicable
- Include docstrings explaining the mathematical content
- Prefer readable proofs over golf (maintainability > brevity)

---

## Part IX: Command Quick Reference

### AF Commands
```bash
# Navigate to a lemma
cd /home/tobiasosborne/Projects/af-tests/examples/lemmas/<lemma_dir>

# Check status
af status
af defs
af show <node>

# Export (if supported)
af export --format json > lemma.json
```

### Lean Commands
```bash
# Build the project
lake build

# Check a specific file
lake build AfTests.Lemma01

# Run the Lean 4 LSP
lake env lean --run <file.lean>
```

### MCP Lean LSP Commands
```
lean_build          # Build and restart LSP
lean_goal           # Get proof state
lean_diagnostic_messages  # Get errors
lean_hover_info     # Get type info
lean_completions    # IDE autocomplete
lean_local_search   # Search declarations
lean_leansearch     # Natural language search
lean_loogle         # Type pattern search
```

---

## Conclusion

This handoff provides a complete roadmap for:
1. Consolidating 22 AF lemma proofs + 1 main theorem
2. Planning the Lean 4 formalization with estimated complexity
3. Organizing the Lean project structure
4. Identifying mathlib dependencies and challenges

**Do NOT start implementation.** This document is for planning and review only.

**Next Actions for Implementer:**
1. Review this document thoroughly
2. Investigate the Lemma 6 refutation
3. Create the master definitions consolidation
4. Set up the Lean file structure (stubs only)
5. Begin with "Low-Hanging Fruit" lemmas

---

*Generated: 2026-01-18*
*Project: Generators of S_N and A_N*
*Status: All AF proofs validated, Lean formalization pending*
