# Implementation Plan: Lean 4 Formalization of S_N/A_N Generator Theorem

## Goal

Prove in Lean 4 (with no sorries and no axioms, except Jordan's Theorem if unavailable in mathlib):

> Let H = ⟨g₁, g₂, g₃⟩ ⊆ Perm(Ω) where Ω = {1,...,6+n+k+m}.
> If n+k+m ≥ 1, then H = Aₙ if n,k,m all odd, else H = Sₙ.

---

## Project Rules

### Rule 1: 200 LOC Maximum Per Module
- **Every Lean file must be ≤ 200 lines of code**
- If an agent notices a file exceeds 200 LOC → **register beads issue as P0/P1** for refactoring
- Command: `bd new -p P0 -t "Refactor: <File>.lean exceeds 200 LOC"`

### Rule 2: Mathlib First
- Use existing mathlib lemmas whenever possible
- Search tools: `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_local_search`
- Verify lemma exists with `lean_hover_info` before using

### Rule 3: Phase-Gated Sorries/Axioms
- **Phase 1-2**: Sorries and axioms ARE allowed (scaffolding)
- **Phase 3**: All sorries and axioms MUST be eliminated (except Jordan if unavailable)

---

## Phase 1: Project Structure Setup

**Goal**: Create scaffolding with one file per lemma, all compiling with sorries.

### Step 1.1: Create Directory Structure

```bash
mkdir -p AfTests/Core
mkdir -p AfTests/BaseCase
mkdir -p AfTests/Transitivity
mkdir -p AfTests/ThreeCycle
mkdir -p AfTests/Primitivity
mkdir -p AfTests/SignAnalysis
```

### Step 1.2: Create Core/Omega.lean

**File**: `AfTests/Core/Omega.lean`
**Purpose**: Define the domain Ω(n,k,m) = Fin(6+n+k+m)
**LOC Target**: ~30

```lean
import Mathlib.Data.Fin.Basic

/-- The domain Ω for parameters n, k, m is Fin (6 + n + k + m) -/
abbrev Omega (n k m : ℕ) := Fin (6 + n + k + m)

/-- The size of Ω -/
def Omega.card (n k m : ℕ) : ℕ := 6 + n + k + m

/-- Core points are {0,1,2,3,4,5} (representing {1,2,3,4,5,6} in 1-indexed) -/
def isCore {n k m : ℕ} (x : Omega n k m) : Prop := x.val < 6

/-- Tail A points are {6, ..., 6+n-1} -/
def isTailA {n k m : ℕ} (x : Omega n k m) : Prop := 6 ≤ x.val ∧ x.val < 6 + n

/-- Tail B points are {6+n, ..., 6+n+k-1} -/
def isTailB {n k m : ℕ} (x : Omega n k m) : Prop := 6 + n ≤ x.val ∧ x.val < 6 + n + k

/-- Tail C points are {6+n+k, ..., 6+n+k+m-1} -/
def isTailC {n k m : ℕ} (x : Omega n k m) : Prop := 6 + n + k ≤ x.val ∧ x.val < 6 + n + k + m
```

**Steps**:
1. [ ] Create file `AfTests/Core/Omega.lean`
2. [ ] Add imports for `Mathlib.Data.Fin.Basic`
3. [ ] Define `Omega` as `abbrev Omega (n k m : ℕ) := Fin (6 + n + k + m)`
4. [ ] Define `Omega.card`
5. [ ] Define predicates `isCore`, `isTailA`, `isTailB`, `isTailC`
6. [ ] Verify `lake build AfTests.Core.Omega` succeeds
7. [ ] Verify LOC ≤ 200

### Step 1.3: Create Core/Generators.lean

**File**: `AfTests/Core/Generators.lean`
**Purpose**: Define generators g₁, g₂, g₃
**LOC Target**: ~80

**Generator definitions from proof_master.md**:
- g₁ = (1 6 4 3 a₁ ... aₙ) = (0 5 3 2 6 7 ... 5+n) in 0-indexed
- g₂ = (2 4 5 1 b₁ ... bₖ) = (1 3 4 0 6+n ... 5+n+k) in 0-indexed
- g₃ = (3 5 6 2 c₁ ... cₘ) = (2 4 5 1 6+n+k ... 5+n+k+m) in 0-indexed

**Steps**:
1. [ ] Create file `AfTests/Core/Generators.lean`
2. [ ] Import `AfTests.Core.Omega`
3. [ ] Import `Mathlib.GroupTheory.Perm.Cycle.Concrete`
4. [ ] Define helper to build cycle from list of `Fin n` values
5. [ ] Define `g₁ (n k m : ℕ) : Perm (Omega n k m)`
6. [ ] Define `g₂ (n k m : ℕ) : Perm (Omega n k m)`
7. [ ] Define `g₃ (n k m : ℕ) : Perm (Omega n k m)`
8. [ ] Add docstrings explaining 1-indexed to 0-indexed mapping
9. [ ] Verify `lake build AfTests.Core.Generators` succeeds
10. [ ] Verify LOC ≤ 200

### Step 1.4: Create Core/GroupH.lean

**File**: `AfTests/Core/GroupH.lean`
**Purpose**: Define H = Subgroup.closure {g₁, g₂, g₃}
**LOC Target**: ~40

**Steps**:
1. [ ] Create file `AfTests/Core/GroupH.lean`
2. [ ] Import `AfTests.Core.Generators`
3. [ ] Import `Mathlib.GroupTheory.Subgroup.Basic`
4. [ ] Define `H (n k m : ℕ) : Subgroup (Perm (Omega n k m))`
5. [ ] Define `H₆ : Subgroup (Perm (Fin 6))` (base case n=k=m=0)
6. [ ] Add basic membership lemmas (g₁ ∈ H, g₂ ∈ H, g₃ ∈ H)
7. [ ] Verify `lake build AfTests.Core.GroupH` succeeds
8. [ ] Verify LOC ≤ 200

### Step 1.5: Create Core/Blocks.lean

**File**: `AfTests/Core/Blocks.lean`
**Purpose**: Define block system B₀ = {{1,4}, {2,5}, {3,6}}
**LOC Target**: ~50

**Steps**:
1. [ ] Create file `AfTests/Core/Blocks.lean`
2. [ ] Import `Mathlib.Data.Finset.Basic`
3. [ ] Define `Block1 : Finset (Fin 6) := {0, 3}` (representing {1,4})
4. [ ] Define `Block2 : Finset (Fin 6) := {1, 4}` (representing {2,5})
5. [ ] Define `Block3 : Finset (Fin 6) := {2, 5}` (representing {3,6})
6. [ ] Define `B₀ : Finset (Finset (Fin 6))` as the partition
7. [ ] Add lemma stubs for block properties (disjoint, union = univ)
8. [ ] Verify `lake build AfTests.Core.Blocks` succeeds
9. [ ] Verify LOC ≤ 200

### Step 1.6: Create Core.lean (Root Module)

**File**: `AfTests/Core.lean`
**Purpose**: Re-export all Core modules

**Steps**:
1. [ ] Create file `AfTests/Core.lean`
2. [ ] Add: `import AfTests.Core.Omega`
3. [ ] Add: `import AfTests.Core.Generators`
4. [ ] Add: `import AfTests.Core.GroupH`
5. [ ] Add: `import AfTests.Core.Blocks`
6. [ ] Verify `lake build AfTests.Core` succeeds

### Step 1.7: Create BaseCase/Lemma01.lean

**File**: `AfTests/BaseCase/Lemma01.lean`
**Purpose**: Block preservation - h_i(B_j) = B_j for all generators
**Proof Strategy**: `native_decide` on Fin 6

**Steps**:
1. [ ] Create file `AfTests/BaseCase/Lemma01.lean`
2. [ ] Import `AfTests.Core`
3. [ ] State theorem: for each generator h and block B, h(B) = B
4. [ ] Add `sorry` placeholder
5. [ ] Add docstring referencing proof_master.md Lemma 1
6. [ ] Verify compilation

### Step 1.8: Create BaseCase/Lemma02.lean

**File**: `AfTests/BaseCase/Lemma02.lean`
**Purpose**: Induced action φ: H₆ → S₃ is surjective
**Proof Strategy**: Construct homomorphism, show surjective

**Steps**:
1. [ ] Create file `AfTests/BaseCase/Lemma02.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Import `Mathlib.GroupTheory.Perm.Basic`
4. [ ] Define `φ : H₆ →* Perm (Fin 3)` as induced action on blocks
5. [ ] State theorem: `Function.Surjective φ`
6. [ ] Add `sorry` placeholder
7. [ ] Add docstring referencing proof_master.md Lemma 2
8. [ ] Verify compilation

### Step 1.9: Create BaseCase/Lemma03.lean

**File**: `AfTests/BaseCase/Lemma03.lean`
**Purpose**: H₆ ≅ S₄, acts imprimitively
**Proof Strategy**: Show |H₆| = 24 and structure matches S₄

**Steps**:
1. [ ] Create file `AfTests/BaseCase/Lemma03.lean`
2. [ ] Import `AfTests.Core`
3. [ ] State theorem: `H₆ ≃* Equiv.Perm (Fin 4)` (group isomorphism)
4. [ ] Add `sorry` placeholder
5. [ ] Add docstring referencing proof_master.md Lemma 3
6. [ ] Verify compilation

### Step 1.10: Create BaseCase/Lemma04.lean

**File**: `AfTests/BaseCase/Lemma04.lean`
**Purpose**: |H₆| = 24 < 360 = |A₆|, so H₆ ≠ A₆, S₆
**Proof Strategy**: Cardinality comparison

**Steps**:
1. [ ] Create file `AfTests/BaseCase/Lemma04.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Import `Mathlib.GroupTheory.SpecificGroups.Alternating`
4. [ ] State theorem: `Fintype.card H₆ = 24`
5. [ ] State theorem: `H₆ ≠ alternatingGroup (Fin 6)`
6. [ ] State theorem: `H₆ ≠ ⊤` (not full symmetric group)
7. [ ] Add `sorry` placeholders
8. [ ] Verify compilation

### Step 1.11: Create Transitivity/Lemma05.lean

**File**: `AfTests/Transitivity/Lemma05.lean`
**Purpose**: H acts transitively on Ω via support graph connectivity
**Proof Strategy**: Define support graph, prove connected, derive transitivity

**Steps**:
1. [ ] Create file `AfTests/Transitivity/Lemma05.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Import `Mathlib.Combinatorics.SimpleGraph.Connectivity`
4. [ ] Import `Mathlib.GroupTheory.GroupAction.Basic`
5. [ ] Define support graph: vertices = Ω, edges = {x,y} if ∃g∈{g₁,g₂,g₃}, g(x)=y or g(y)=x
6. [ ] State theorem: support graph is connected (when n+k+m ≥ 1)
7. [ ] State theorem: `MulAction.IsPretransitive H (Omega n k m)`
8. [ ] Add `sorry` placeholders
9. [ ] Verify compilation

### Step 1.12: Create ThreeCycle/Lemma06.lean

**File**: `AfTests/ThreeCycle/Lemma06.lean`
**Purpose**: [g₁, g₂] = (1 7 5)(2 4 6) (corrected value from proof_master.md v2.0)
**Proof Strategy**: `native_decide`

**Steps**:
1. [ ] Create file `AfTests/ThreeCycle/Lemma06.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Import `Mathlib.GroupTheory.Perm.Cycle.Concrete`
4. [ ] Define `c₁₂ : Perm (Fin 7) := g₁⁻¹ * g₂⁻¹ * g₁ * g₂` (for n=1, k=m=0)
5. [ ] State theorem: `c₁₂ = c[0, 6, 4] * c[1, 3, 5]` (0-indexed for (1 7 5)(2 4 6))
6. [ ] Add `sorry` placeholder (will use `native_decide`)
7. [ ] Add docstring noting correction from original
8. [ ] Verify compilation

### Step 1.13: Create ThreeCycle/Lemma07.lean

**File**: `AfTests/ThreeCycle/Lemma07.lean`
**Purpose**: [g₁, g₃] = (1 5 6)(2 3 4)
**Proof Strategy**: `native_decide`

**Steps**:
1. [ ] Create file `AfTests/ThreeCycle/Lemma07.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Define `c₁₃ : Perm (Fin 7)` for appropriate parameters
4. [ ] State theorem: `c₁₃ = c[0, 4, 5] * c[1, 2, 3]` (0-indexed)
5. [ ] Add `sorry` placeholder
6. [ ] Verify compilation

### Step 1.14: Create ThreeCycle/Lemma08.lean

**File**: `AfTests/ThreeCycle/Lemma08.lean`
**Purpose**: [g₂, g₃] = (1 6 2)(3 5 4)
**Proof Strategy**: `native_decide`

**Steps**:
1. [ ] Create file `AfTests/ThreeCycle/Lemma08.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Define `c₂₃ : Perm (Fin 7)` for appropriate parameters
4. [ ] State theorem: `c₂₃ = c[0, 5, 1] * c[2, 4, 3]` (0-indexed)
5. [ ] Add `sorry` placeholder
6. [ ] Verify compilation

### Step 1.15: Create ThreeCycle/Lemma09.lean

**File**: `AfTests/ThreeCycle/Lemma09.lean`
**Purpose**: (c₁₂ · c₁₃⁻¹)² = (1 6 2), a single 3-cycle
**Proof Strategy**: `native_decide`

**Steps**:
1. [ ] Create file `AfTests/ThreeCycle/Lemma09.lean`
2. [ ] Import `AfTests.ThreeCycle.Lemma06`
3. [ ] Import `AfTests.ThreeCycle.Lemma07`
4. [ ] Import `AfTests.ThreeCycle.Lemma08`
5. [ ] Define extraction formula
6. [ ] State theorem: result is a single 3-cycle `c[0, 5, 1]`
7. [ ] State theorem: this 3-cycle is in H
8. [ ] Add `sorry` placeholders
9. [ ] Verify compilation

### Step 1.16: Create Primitivity/Lemma10.lean

**File**: `AfTests/Primitivity/Lemma10.lean`
**Purpose**: Primitivity criterion - primitive ⟺ no non-trivial partition ⟺ maximal stabilizer
**Proof Strategy**: Use mathlib's `MulAction.IsPrimitive`

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma10.lean`
2. [ ] Import `AfTests.Core`
3. [ ] Import `Mathlib.GroupTheory.GroupAction.Primitive`
4. [ ] State equivalence between primitivity definitions
5. [ ] Add `sorry` placeholder
6. [ ] Verify compilation

### Step 1.17: Create Primitivity/Lemma11_1.lean

**File**: `AfTests/Primitivity/Lemma11_1.lean`
**Purpose**: B₀ is the only non-trivial block system for H₆
**Proof Strategy**: Enumerate partitions, verify

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11_1.lean`
2. [ ] Import `AfTests.Core`
3. [ ] State theorem: any H₆-invariant partition is trivial or equals B₀
4. [ ] Add `sorry` placeholder
5. [ ] Verify compilation

### Step 1.18: Create Primitivity/Lemma11_2.lean

**File**: `AfTests/Primitivity/Lemma11_2.lean`
**Purpose**: Cycle fixing block implies support ⊆ B or disjoint
**Proof Strategy**: Case analysis on cycle structure

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11_2.lean`
2. [ ] Import `AfTests.Core`
3. [ ] State theorem about cycle support and blocks
4. [ ] Add `sorry` placeholder
5. [ ] Verify compilation

### Step 1.19: Create Primitivity/Lemma11_3.lean

**File**: `AfTests/Primitivity/Lemma11_3.lean`
**Purpose**: If g₁(B) = B with a₁ ∈ B, then supp(g₁) ⊆ B
**Proof Strategy**: Apply Lemma 11.2

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11_3.lean`
2. [ ] Import `AfTests.Primitivity.Lemma11_2`
3. [ ] State theorem
4. [ ] Add `sorry` placeholder
5. [ ] Verify compilation

### Step 1.20: Create Primitivity/Lemma11_4.lean

**File**: `AfTests/Primitivity/Lemma11_4.lean`
**Purpose**: Block orbit size divides cycle length
**Proof Strategy**: Orbit-stabilizer theorem

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11_4.lean`
2. [ ] Import `AfTests.Core`
3. [ ] State theorem about orbit sizes
4. [ ] Add `sorry` placeholder
5. [ ] Verify compilation

### Step 1.21: Create Primitivity/Lemma11_5.lean

**File**: `AfTests/Primitivity/Lemma11_5.lean`
**Purpose**: n+k+m ≥ 1 implies no non-trivial block system
**Proof Strategy**: Contradiction via case analysis

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11_5.lean`
2. [ ] Import `AfTests.Primitivity.Lemma11_1` through `Lemma11_4`
3. [ ] State theorem: `n + k + m ≥ 1 → ¬∃ B, IsNontrivialBlockSystem H B`
4. [ ] Add `sorry` placeholder
5. [ ] Verify compilation

### Step 1.22: Create Primitivity/Lemma11.lean

**File**: `AfTests/Primitivity/Lemma11.lean`
**Purpose**: n+k+m ≥ 1 implies H acts primitively
**Proof Strategy**: Combine Lemmas 5, 10, 11.5

**Steps**:
1. [ ] Create file `AfTests/Primitivity/Lemma11.lean`
2. [ ] Import all Lemma11_* files
3. [ ] Import `AfTests.Transitivity.Lemma05`
4. [ ] State theorem: `n + k + m ≥ 1 → MulAction.IsPrimitive H (Omega n k m)`
5. [ ] Add `sorry` placeholder
6. [ ] Verify compilation

### Step 1.23: Create SignAnalysis/Lemma12.lean

**File**: `AfTests/SignAnalysis/Lemma12.lean`
**Purpose**: Jordan's Theorem (axiom or mathlib)
**Proof Strategy**: Axiom if not in mathlib

**Steps**:
1. [ ] Create file `AfTests/SignAnalysis/Lemma12.lean`
2. [ ] Search mathlib: `lean_leansearch "Jordan theorem primitive permutation 3-cycle"`
3. [ ] If found: import and use
4. [ ] If not found: declare as axiom with documentation
5. [ ] State: primitive + contains 3-cycle → contains alternating group
6. [ ] Verify compilation

### Step 1.24: Create SignAnalysis/Lemma13.lean

**File**: `AfTests/SignAnalysis/Lemma13.lean`
**Purpose**: l-cycle has sign (-1)^{l-1}
**Proof Strategy**: Use mathlib's `Equiv.Perm.sign_cycle`

**Steps**:
1. [ ] Create file `AfTests/SignAnalysis/Lemma13.lean`
2. [ ] Import `Mathlib.GroupTheory.Perm.Sign`
3. [ ] Search: `lean_loogle "Perm.sign_cycle"`
4. [ ] State theorem using mathlib lemma
5. [ ] Prove using mathlib (should be direct)
6. [ ] Verify compilation

### Step 1.25: Create SignAnalysis/Lemma14.lean

**File**: `AfTests/SignAnalysis/Lemma14.lean`
**Purpose**: sign(g_i) = (-1)^{tail_i + 3}
**Proof Strategy**: Apply Lemma 13 to each generator

**Steps**:
1. [ ] Create file `AfTests/SignAnalysis/Lemma14.lean`
2. [ ] Import `AfTests.SignAnalysis.Lemma13`
3. [ ] Import `AfTests.Core.Generators`
4. [ ] State theorem for g₁: `Perm.sign (g₁ n k m) = (-1)^(n + 3)`
5. [ ] State theorem for g₂: `Perm.sign (g₂ n k m) = (-1)^(k + 3)`
6. [ ] State theorem for g₃: `Perm.sign (g₃ n k m) = (-1)^(m + 3)`
7. [ ] Add `sorry` placeholders
8. [ ] Verify compilation

### Step 1.26: Create SignAnalysis/Lemma15.lean

**File**: `AfTests/SignAnalysis/Lemma15.lean`
**Purpose**: G = A_n iff all generators even; G = S_n iff contains odd
**Proof Strategy**: Index-2 subgroup argument

**Steps**:
1. [ ] Create file `AfTests/SignAnalysis/Lemma15.lean`
2. [ ] Import `AfTests.SignAnalysis.Lemma14`
3. [ ] Import `Mathlib.GroupTheory.SpecificGroups.Alternating`
4. [ ] State theorem: all even → H ≤ alternatingGroup
5. [ ] State theorem: contains odd + Jordan → H = ⊤
6. [ ] Add `sorry` placeholders
7. [ ] Verify compilation

### Step 1.27: Create MainTheorem.lean

**File**: `AfTests/MainTheorem.lean`
**Purpose**: Final theorem combining all lemmas
**Proof Strategy**: Apply lemmas in sequence

**Steps**:
1. [ ] Create file `AfTests/MainTheorem.lean`
2. [ ] Import all required lemma files
3. [ ] State main theorem:
   ```lean
   theorem main_theorem (n k m : ℕ) (h : n + k + m ≥ 1) :
       H n k m = (if n % 2 = 1 ∧ k % 2 = 1 ∧ m % 2 = 1
                 then alternatingGroup (Omega n k m)
                 else ⊤) := by
     sorry
   ```
4. [ ] Add comprehensive docstring
5. [ ] Verify compilation

### Step 1.28: Update AfTests.lean Root Module

**Steps**:
1. [ ] Edit `AfTests.lean` to import all modules
2. [ ] Verify `lake build` succeeds for entire project
3. [ ] Run `wc -l AfTests/**/*.lean | sort -n` to verify all files ≤ 200 LOC

### Phase 1 Completion Checklist

- [ ] `AfTests/Core/Omega.lean` created and compiles
- [ ] `AfTests/Core/Generators.lean` created and compiles
- [ ] `AfTests/Core/GroupH.lean` created and compiles
- [ ] `AfTests/Core/Blocks.lean` created and compiles
- [ ] `AfTests/Core.lean` created and compiles
- [ ] `AfTests/BaseCase/Lemma01.lean` created and compiles
- [ ] `AfTests/BaseCase/Lemma02.lean` created and compiles
- [ ] `AfTests/BaseCase/Lemma03.lean` created and compiles
- [ ] `AfTests/BaseCase/Lemma04.lean` created and compiles
- [ ] `AfTests/Transitivity/Lemma05.lean` created and compiles
- [ ] `AfTests/ThreeCycle/Lemma06.lean` created and compiles
- [ ] `AfTests/ThreeCycle/Lemma07.lean` created and compiles
- [ ] `AfTests/ThreeCycle/Lemma08.lean` created and compiles
- [ ] `AfTests/ThreeCycle/Lemma09.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma10.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11_1.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11_2.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11_3.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11_4.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11_5.lean` created and compiles
- [ ] `AfTests/Primitivity/Lemma11.lean` created and compiles
- [ ] `AfTests/SignAnalysis/Lemma12.lean` created and compiles
- [ ] `AfTests/SignAnalysis/Lemma13.lean` created and compiles
- [ ] `AfTests/SignAnalysis/Lemma14.lean` created and compiles
- [ ] `AfTests/SignAnalysis/Lemma15.lean` created and compiles
- [ ] `AfTests/MainTheorem.lean` created and compiles
- [ ] `lake build` succeeds
- [ ] All files ≤ 200 LOC

---

## Phase 2: Compilation with Sorries/Axioms

**Goal**: Replace stub sorries with real proofs OR explicit `sorry`/`axiom` markers.

### Wave 2.1: Core Infrastructure Refinement

#### Step 2.1.1: Finalize Omega.lean
1. [ ] Add any missing utility lemmas for Fin arithmetic
2. [ ] Ensure coercions work smoothly
3. [ ] Test with `#check` and `#eval` where applicable
4. [ ] Verify no sorries remain

#### Step 2.1.2: Finalize Generators.lean
1. [ ] Implement g₁ using cycle notation `c[...]`
2. [ ] Handle the variable-length tail: `[0, 5, 3, 2] ++ (List.range n).map (· + 6)`
3. [ ] Implement g₂ similarly
4. [ ] Implement g₃ similarly
5. [ ] Add `native_decide` tests for base case (n=k=m=0)
6. [ ] Verify generators are well-defined permutations

#### Step 2.1.3: Finalize GroupH.lean
1. [ ] Verify `Subgroup.closure` works correctly
2. [ ] Prove `g₁ ∈ H`, `g₂ ∈ H`, `g₃ ∈ H`
3. [ ] Add helper lemmas for membership

#### Step 2.1.4: Finalize Blocks.lean
1. [ ] Prove blocks are pairwise disjoint
2. [ ] Prove blocks cover Fin 6
3. [ ] Define block membership function

### Wave 2.2: Sign Analysis (Quick Wins)

#### Step 2.2.1: Complete Lemma13.lean
1. [ ] Search mathlib: `lean_loogle "Perm.sign IsCycle"`
2. [ ] Find `Equiv.Perm.sign_cycle` or equivalent
3. [ ] State and prove: sign of l-cycle is (-1)^(l-1)
4. [ ] Should complete with no sorries

#### Step 2.2.2: Complete Lemma14.lean
1. [ ] Use Lemma 13 to compute sign of g₁
2. [ ] g₁ is a (4+n)-cycle, so sign = (-1)^(3+n)
3. [ ] Similarly for g₂ (4+k)-cycle and g₃ (4+m)-cycle
4. [ ] May need `native_decide` for specific cases
5. [ ] Target: no sorries

### Wave 2.3: Base Case Lemmas (Computational)

#### Step 2.3.1: Complete Lemma01.lean
1. [ ] For n=k=m=0, define g₁, g₂, g₃ on Fin 6
2. [ ] For each generator h ∈ {g₁, g₂, g₃} and block B ∈ B₀:
   - Prove `h '' B = B` using `native_decide`
3. [ ] May need ~9 individual theorems (3 generators × 3 blocks)
4. [ ] Target: no sorries

#### Step 2.3.2: Complete Lemma04.lean
1. [ ] Compute |H₆| by enumeration or structure analysis
2. [ ] Prove `Fintype.card H₆ = 24` (may need computation)
3. [ ] Prove `24 < 360` trivially
4. [ ] Derive H₆ ≠ A₆, H₆ ≠ S₆
5. [ ] Target: no sorries (computational)

#### Step 2.3.3: Complete Lemma02.lean
1. [ ] Define homomorphism φ: H₆ → Perm (Fin 3)
2. [ ] φ sends each generator to its induced permutation on blocks
3. [ ] Show image contains (0 1), (0 1 2) → generates S₃
4. [ ] Prove surjectivity
5. [ ] May have some sorries for structural lemmas

#### Step 2.3.4: Complete Lemma03.lean
1. [ ] Use |H₆| = 24 from Lemma 4
2. [ ] Use ker(φ) analysis from Lemma 2
3. [ ] Show H₆ ≅ S₄ via explicit isomorphism or structure theorem
4. [ ] May have sorries for isomorphism construction

### Wave 2.4: Commutators and 3-Cycle (Computational)

#### Step 2.4.1: Complete Lemma06.lean
1. [ ] Reference existing `ThreeCycleExtraction.lean` for patterns
2. [ ] Define c₁₂ = [g₁, g₂] = g₁⁻¹ * g₂⁻¹ * g₁ * g₂
3. [ ] For n=1, k=m=0, work in Fin 7
4. [ ] Prove `c₁₂ = c[0, 6, 4] * c[1, 3, 5]` via `native_decide`
5. [ ] Target: no sorries

#### Step 2.4.2: Complete Lemma07.lean
1. [ ] Define c₁₃ = [g₁, g₃]
2. [ ] Prove equals (1 5 6)(2 3 4) in 1-indexed = c[0, 4, 5] * c[1, 2, 3]
3. [ ] Use `native_decide`
4. [ ] Target: no sorries

#### Step 2.4.3: Complete Lemma08.lean
1. [ ] Define c₂₃ = [g₂, g₃]
2. [ ] Prove equals (1 6 2)(3 5 4) in 1-indexed = c[0, 5, 1] * c[2, 4, 3]
3. [ ] Use `native_decide`
4. [ ] Target: no sorries

#### Step 2.4.4: Complete Lemma09.lean
1. [ ] Use c₁₂, c₁₃ from Lemmas 6, 7
2. [ ] Compute extraction: (c₁₂ · c₁₃²⁻¹) or similar
3. [ ] Prove result is single 3-cycle
4. [ ] Prove 3-cycle is in H
5. [ ] Use `native_decide`
6. [ ] Target: no sorries

### Wave 2.5: Transitivity

#### Step 2.5.1: Complete Lemma05.lean
1. [ ] Define support graph formally
2. [ ] For n+k+m ≥ 1, show graph is connected
3. [ ] Core connected: 1-2-3-4-5-6-1 via generators
4. [ ] Tails connected to core via generator definitions
5. [ ] Derive transitivity from connectivity
6. [ ] May have sorries for graph theory

### Wave 2.6: Primitivity Chain

#### Step 2.6.1: Complete Lemma10.lean
1. [ ] Use mathlib's primitivity definitions
2. [ ] State equivalence of characterizations
3. [ ] May be able to use existing mathlib theorems directly
4. [ ] Target: minimal sorries

#### Step 2.6.2: Complete Lemma11_1.lean
1. [ ] Enumerate all partitions of Fin 6
2. [ ] Check H₆-invariance for each
3. [ ] Show only trivial and B₀ are invariant
4. [ ] Computational approach with `native_decide`
5. [ ] May have sorries

#### Step 2.6.3: Complete Lemma11_2.lean through Lemma11_5.lean
1. [ ] Follow proof_master.md structure
2. [ ] Lemma 11.2: general cycle/block relationship
3. [ ] Lemma 11.3: apply to g₁ with tail
4. [ ] Lemma 11.4: orbit-stabilizer for blocks
5. [ ] Lemma 11.5: combine for contradiction
6. [ ] Likely to have sorries (hardest lemmas)

#### Step 2.6.4: Complete Lemma11.lean
1. [ ] Combine Lemmas 5, 10, 11.5
2. [ ] Derive primitivity for n+k+m ≥ 1
3. [ ] May have sorries depending on sub-lemmas

### Wave 2.7: Jordan and Conclusion

#### Step 2.7.1: Complete Lemma12.lean
1. [ ] Search mathlib thoroughly:
   - `lean_leansearch "primitive permutation group 3-cycle alternating"`
   - `lean_loogle "IsPrimitive alternatingGroup"`
2. [ ] If found: use it
3. [ ] If not found: declare axiom:
   ```lean
   axiom jordan_theorem ...
   ```
4. [ ] Document clearly

#### Step 2.7.2: Complete Lemma15.lean
1. [ ] Use sign analysis from Lemma 14
2. [ ] Case 1: all odd tails → all generators even → H ≤ A_n
3. [ ] Case 2: some even tail → some generator odd → H contains odd element
4. [ ] Apply Jordan (Lemma 12) + odd element → H = S_n
5. [ ] May have sorries for index arguments

#### Step 2.7.3: Complete MainTheorem.lean
1. [ ] Import all lemmas
2. [ ] Structure proof:
   - n+k+m ≥ 1 (hypothesis)
   - H is transitive (Lemma 5)
   - H is primitive (Lemma 11)
   - H contains 3-cycle (Lemma 9)
   - By Jordan (Lemma 12), A_n ≤ H
   - Parity analysis (Lemmas 14, 15) determines A_n or S_n
3. [ ] May have sorries for final integration

### Phase 2 Completion Checklist

- [ ] `lake build` succeeds
- [ ] All lemma statements match proof_master.md
- [ ] All dependencies explicit in imports
- [ ] Sorries clearly marked with `-- TODO:` comments
- [ ] All files ≤ 200 LOC
- [ ] Create beads issues for remaining sorries: `bd new -p P1 -t "Eliminate sorry: <file>:<line>"`

---

## Phase 3: Sorry/Axiom Elimination

**Goal**: Remove all sorries. Jordan's Theorem may remain as axiom if unavailable.

### Step 3.1: Audit Current State

1. [ ] Run `grep -rn "sorry" AfTests/ --include="*.lean" > sorries.txt`
2. [ ] Count sorries: `wc -l sorries.txt`
3. [ ] Categorize by difficulty:
   - Easy: should be `native_decide` or direct mathlib
   - Medium: requires proof construction
   - Hard: requires new lemmas or complex reasoning
4. [ ] Create beads issues for each sorry

### Step 3.2: Eliminate Easy Sorries

For each sorry marked "Easy":
1. [ ] Try `native_decide`
2. [ ] Try `decide`
3. [ ] Try `simp`
4. [ ] Try `omega`
5. [ ] Search mathlib with `exact?` or `apply?`
6. [ ] If solved, remove sorry and verify build

### Step 3.3: Eliminate Medium Sorries

For each sorry marked "Medium":
1. [ ] Analyze goal with `lean_goal`
2. [ ] Search mathlib: `lean_leansearch`, `lean_loogle`
3. [ ] Break into helper lemmas if needed
4. [ ] Use `calc` for equational reasoning
5. [ ] Use `have` for intermediate steps
6. [ ] If solved, remove sorry and verify build
7. [ ] If stuck, create beads issue: `bd new -p P1 -t "Blocked: <lemma> - <reason>"`

### Step 3.4: Eliminate Hard Sorries

For each sorry marked "Hard":
1. [ ] Review proof_master.md for insight
2. [ ] Consider alternative proof strategies
3. [ ] Search for related mathlib theorems
4. [ ] May need to split into smaller lemmas
5. [ ] May need to add auxiliary definitions
6. [ ] Document any fundamental obstacles

### Step 3.5: Handle Jordan's Theorem

1. [ ] Final mathlib search for Jordan's theorem
2. [ ] If found: replace axiom with proof using mathlib
3. [ ] If not found: keep as axiom with documentation:
   ```lean
   /-- Jordan's Theorem: A primitive permutation group of degree ≥ 5
       containing a 3-cycle contains the alternating group.

       This is a classical result (Jordan, 1873). It is not currently
       in mathlib as of v4.26.0.

       Reference: Wielandt, "Finite Permutation Groups", Theorem 13.9
   -/
   axiom jordan_theorem ...
   ```

### Step 3.6: Final Verification

1. [ ] Run `grep -rn "sorry" AfTests/ --include="*.lean"`
   - Should return empty (or only Jordan if axiom)
2. [ ] Run `lake build`
   - Should succeed with no errors
3. [ ] Run `lake build` with warnings enabled
   - Should have no warnings
4. [ ] Verify main theorem:
   ```lean
   #check @main_theorem
   ```
5. [ ] Verify no unexpected axioms:
   ```lean
   #print axioms main_theorem
   ```
   - Should show only `jordan_theorem` (if used) and standard axioms

### Step 3.7: Documentation and Cleanup

1. [ ] Add module docstrings to all files
2. [ ] Ensure all theorems have docstrings
3. [ ] Verify consistent naming conventions
4. [ ] Remove any dead code
5. [ ] Final LOC check: `wc -l AfTests/**/*.lean | sort -n`

### Phase 3 Completion Checklist

- [ ] Zero sorries (except Jordan if unavailable)
- [ ] `lake build` succeeds
- [ ] No build warnings
- [ ] `#check main_theorem` works
- [ ] `#print axioms main_theorem` shows only expected axioms
- [ ] All files ≤ 200 LOC
- [ ] All beads issues closed: `bd list` shows no open P0/P1

---

## Appendix A: Mathlib Key Imports

```lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
```

---

## Appendix B: Index Convention

The AF proofs use 1-indexed elements (1,2,3,4,5,6,a₁,...).
Lean's `Fin n` is 0-indexed.

**Mapping**: Element k in AF → `Fin.mk (k-1)` in Lean

| AF (1-indexed) | Lean (0-indexed) |
|----------------|------------------|
| 1 | 0 |
| 2 | 1 |
| 3 | 2 |
| 4 | 3 |
| 5 | 4 |
| 6 | 5 |
| 7 (= a₁) | 6 |

Example cycles:
- AF (1 6 4 3) → Lean `c[0, 5, 3, 2]`
- AF (1 7 5)(2 4 6) → Lean `c[0, 6, 4] * c[1, 3, 5]`

---

## Appendix C: Commands Quick Reference

```bash
# Build
lake build
lake build AfTests.Core.Omega

# Find sorries
grep -rn "sorry" AfTests/ --include="*.lean"

# LOC check
wc -l AfTests/**/*.lean | sort -n

# Beads
bd new -p P1 -t "Title"
bd list
bd list -p P0
bd close <id>

# MCP Lean tools
lean_goal <file> <line>
lean_diagnostic_messages <file>
lean_hover_info <file> <line> <col>
lean_loogle "query"
lean_leansearch "natural language query"
lean_local_search "declaration name"
```

---

## Appendix D: Success Metrics

| Metric | Target |
|--------|--------|
| Total Sorries | 0 (or 1 for Jordan) |
| Axioms | 0 (or 1 for Jordan) |
| Max LOC per file | ≤ 200 |
| Build warnings | 0 |
| Main theorem compiles | ✓ |
| Open P0/P1 issues | 0 |

---

*Document Version: 2.0*
*Last Updated: 2026-01-18*
