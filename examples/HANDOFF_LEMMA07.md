# Handoff: Proving Lemma 07 (Commutator [g₁, g₃])

## Overview

This document provides detailed guidance for the next agent proving Lemma 07 using the `af` (Adversarial Proof Framework) tool.

**Lemma 07 Location:** `./lemmas/lemma07_commutator_g1g3/`

**Lemma 07 Statement:** Let g₁ = (1 6 4 3 7) and g₃ = (5 6 2 3) in S₇ (case n=1, k=m=0). Then [g₁, g₃] := g₁⁻¹ g₃⁻¹ g₁ g₃ = (1 5 6)(2 3 4).

**Dependencies:** None (this is a direct computation).

**Reference:** See `./proof_master.md` for the complete proof structure and all lemma statements (Lemma 7 is in Part III: Commutator Computations, lines 173-211).

---

## IMPORTANT: Lessons from Lemma 06

During the proof of Lemma 06, we discovered that the **original** proof_master.md contained computational errors in ALL commutator lemmas (6, 7, 8). The document has been **corrected** (Version 2.0).

**Key lesson:** Always verify computations step-by-step. Do NOT trust pre-computed results without verification.

The corrected results are:
- **Lemma 6:** [g₁, g₂] = (1 7 5)(2 4 6) — **VERIFIED** ✓
- **Lemma 7:** [g₁, g₃] = (1 5 6)(2 3 4) — **VERIFIED** ✓
- **Lemma 8:** [g₂, g₃] = (1 6 2)(3 5 4) — **VERIFIED** ✓
- **Lemma 9:** (c₁₂ · c₁₃⁻¹)² = (1 6 2) — pending (see HANDOFF_LEMMA09.md)

---

## Proof Chain So Far

The following lemmas have been validated and can be cited if needed:

| Lemma | Location | Statement | Status |
|-------|----------|-----------|--------|
| **Lemma 1** | `lemma01_block_preservation/` | B₀ = {{1,4}, {2,5}, {3,6}} is preserved setwise by h₁, h₂, h₃ | VALIDATED |
| **Lemma 2** | `lemma02_induced_action/` | φ: H_6 → S_{B₀} satisfies Im(φ) = S_3 | VALIDATED |
| **Lemma 3** | `lemma03_base_case_structure/` | H_6 ≅ S_4, acting imprimitively on {1,...,6} | VALIDATED |
| **Lemma 4** | `lemma04_base_case_exclusion/` | \|H_6\| = 24 < 360 = \|A_6\|, hence H_6 ∉ {A_6, S_6} | VALIDATED |
| **Lemma 5** | `lemma05_transitivity/` | H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω | VALIDATED |
| **Lemma 6** | `lemma06_commutator_g1g2/` | [g₁, g₂] = (1 7 5)(2 4 6) | **REFUTED** (original claim was wrong, but computation verified) |
| **Lemma 7** | `lemma07_commutator_g1g3/` | [g₁, g₃] = (1 5 6)(2 3 4) | **VALIDATED** ✓ |
| **Lemma 8** | `lemma08_commutator_g2g3/` | [g₂, g₃] = (1 6 2)(3 5 4) | **VALIDATED** ✓ |

**Note:** Lemma 6 was REFUTED because the original root statement claimed [g₁, g₂] = (1 2 6)(3 4 5), which is incorrect. The verified result is (1 7 5)(2 4 6). The adversarial process correctly identified this error.

**Next Step:** Proceed to **Lemma 09** (3-cycle extraction). See `./HANDOFF_LEMMA09.md`.

---

## Critical Success Factors (Lessons from Lemma 06)

1. **Spawn parallel verifier agents** - Use `Task` tool with `subagent_type="general-purpose"` to spawn multiple pedantic verifiers in parallel. Never verify inline.

2. **Add definitions FIRST** - Before any proof work, add all necessary definitions using `af def-add`. Verifiers challenge every undefined term.

3. **Show ALL computation steps** - For cycle multiplication, trace each element explicitly. Verifiers will challenge any skipped steps.

4. **Use element trace tables** - Present computations as tables showing each intermediate step.

5. **Iterative refinement** - Expect multiple rounds:
   - Prover writes proof → Verifiers challenge → Prover resolves → Verifiers re-verify → Accept

---

## Proof Strategy for Lemma 07

This lemma requires **direct cycle multiplication**. The proof has these parts:

1. **Define the cycles** g₁ = (1 6 4 3 7) and g₃ = (5 6 2 3)
2. **Compute inverses** g₁⁻¹ = (1 7 3 4 6) and g₃⁻¹ = (5 3 2 6)
3. **Compute the commutator** [g₁, g₃] = g₁⁻¹ g₃⁻¹ g₁ g₃ by tracing each element
4. **Verify the result** is (1 5 6)(2 3 4)

### Commutator Convention

**CRITICAL:** We use [σ, τ] := σ⁻¹ τ⁻¹ σ τ

This means for computing [g₁, g₃](x), we evaluate:
```
[g₁, g₃](x) = g₁⁻¹(g₃⁻¹(g₁(g₃(x))))
```

Apply in order (right-to-left):
1. Apply g₃ to x → get g₃(x)
2. Apply g₁ to that → get g₁(g₃(x))
3. Apply g₃⁻¹ to that → get g₃⁻¹(g₁(g₃(x)))
4. Apply g₁⁻¹ to that → get g₁⁻¹(g₃⁻¹(g₁(g₃(x)))) = [g₁, g₃](x)

### Action Tables

**g₁ = (1 6 4 3 7):**
- 1 → 6, 6 → 4, 4 → 3, 3 → 7, 7 → 1
- Fixes: 2, 5

**g₃ = (5 6 2 3):**
- 5 → 6, 6 → 2, 2 → 3, 3 → 5
- Fixes: 1, 4, 7

**g₁⁻¹ = (1 7 3 4 6):**
- 1 → 7, 7 → 3, 3 → 4, 4 → 6, 6 → 1
- Fixes: 2, 5

**g₃⁻¹ = (5 3 2 6):**
- 5 → 3, 3 → 2, 2 → 6, 6 → 5
- Fixes: 1, 4, 7

### Verified Computation (from proof_master.md v2.0)

| x | g₃(x) | g₁(g₃(x)) | g₃⁻¹(...) | g₁⁻¹(...) | Result |
|---|-------|-----------|-----------|-----------|--------|
| 1 | 1 | 6 | 5 | 5 | 1 → 5 |
| 2 | 3 | 7 | 7 | 3 | 2 → 3 |
| 3 | 5 | 5 | 3 | 4 | 3 → 4 |
| 4 | 4 | 3 | 2 | 2 | 4 → 2 |
| 5 | 6 | 4 | 4 | 6 | 5 → 6 |
| 6 | 2 | 2 | 6 | 1 | 6 → 1 |
| 7 | 7 | 1 | 1 | 7 | 7 → 7 |

**Orbit analysis:**
- Orbit 1: 1 → 5 → 6 → 1 gives (1 5 6)
- Orbit 2: 2 → 3 → 4 → 2 gives (2 3 4)
- Fixed: 7

**Result:** [g₁, g₃] = (1 5 6)(2 3 4)

---

## Step-by-Step Instructions

### Step 1: Navigate and Check Status

```bash
cd /home/tobiasosborne/Projects/af-tests/examples/lemmas/lemma07_commutator_g1g3

# Check current state
af status

# Check existing definitions (should be empty)
af defs
```

### Step 2: Add All Required Definitions

Add these definitions BEFORE any proof work:

```bash
# Domain for this computation (S_7)
af def-add Domain_S7 "The symmetric group S_7 acts on {1, 2, 3, 4, 5, 6, 7}."

# Generator g_1 (specific to n=1, k=m=0 case)
af def-add g_1 "g_1 = (1 6 4 3 7), a 5-cycle in S_7. Action: 1→6→4→3→7→1; fixes 2, 5."

# Generator g_3
af def-add g_3 "g_3 = (5 6 2 3), a 4-cycle in S_7. Action: 5→6→2→3→5; fixes 1, 4, 7."

# Inverse of g_1
af def-add g_1_inv "g_1^{-1} = (1 7 3 4 6), the inverse of g_1. Action: 1→7→3→4→6→1; fixes 2, 5."

# Inverse of g_3
af def-add g_3_inv "g_3^{-1} = (5 3 2 6), the inverse of g_3. Action: 5→3→2→6→5; fixes 1, 4, 7."

# Commutator definition
af def-add Commutator "For permutations σ, τ, the commutator is [σ, τ] := σ^{-1} τ^{-1} σ τ. Evaluated as [σ,τ](x) = σ^{-1}(τ^{-1}(σ(τ(x))))."

# Cycle multiplication convention
af def-add Cycle_Multiplication "When computing σ · τ, we apply τ first, then σ. So (σ · τ)(x) = σ(τ(x))."

# Cycle inverse rule
af def-add Cycle_Inverse "For an ℓ-cycle (a_1 a_2 ... a_ℓ), its inverse is obtained by reversing: (a_ℓ a_{ℓ-1} ... a_1). In standard form: (a_1 a_ℓ a_{ℓ-1} ... a_2)."
```

### Step 3: Claim Root Node and Add Proof Structure

```bash
# Claim root node as prover
af claim 1 --owner prover-1 --role prover

# Refine with overview
af refine 1 --owner prover-1 -s "OVERVIEW: We compute [g_1, g_3] = g_1^{-1} g_3^{-1} g_1 g_3 by tracing all 7 elements of {1,2,3,4,5,6,7} through the composition. Using the convention [σ,τ](x) = σ^{-1}(τ^{-1}(σ(τ(x)))), we trace each element and identify the cycle decomposition."

# Add Part 1: Inverse verification
af refine 1.1 --owner prover-1 --sibling -s "PART 1 - INVERSE VERIFICATION (citing Cycle_Inverse):
By Cycle_Inverse, reversing (1 6 4 3 7) gives (7 3 4 6 1), standard form g_1^{-1} = (1 7 3 4 6).
By Cycle_Inverse, reversing (5 6 2 3) gives (3 2 6 5), standard form g_3^{-1} = (5 3 2 6).
Verification: g_1 maps 1→6, g_1^{-1} maps 6→1. Correct."

# Add Part 2: Action tables
af refine 1.2 --owner prover-1 --sibling -s "PART 2 - ACTION TABLES:
g_1 = (1 6 4 3 7): 1→6, 6→4, 4→3, 3→7, 7→1; fixes 2, 5.
g_3 = (5 6 2 3): 5→6, 6→2, 2→3, 3→5; fixes 1, 4, 7.
g_1^{-1} = (1 7 3 4 6): 1→7, 7→3, 3→4, 4→6, 6→1; fixes 2, 5.
g_3^{-1} = (5 3 2 6): 5→3, 3→2, 2→6, 6→5; fixes 1, 4, 7."

# Add individual element traces (one node per element for easy verification)
af refine 1.3 --owner prover-1 --sibling -s "TRACE x=1: g_3(1)=1 (fixed) → g_1(1)=6 → g_3^{-1}(6)=5 → g_1^{-1}(5)=5 (fixed). Therefore 1 ↦ 5."

af refine 1.4 --owner prover-1 --sibling -s "TRACE x=2: g_3(2)=3 → g_1(3)=7 → g_3^{-1}(7)=7 (fixed) → g_1^{-1}(7)=3. Therefore 2 ↦ 3."

af refine 1.5 --owner prover-1 --sibling -s "TRACE x=3: g_3(3)=5 → g_1(5)=5 (fixed) → g_3^{-1}(5)=3 → g_1^{-1}(3)=4. Therefore 3 ↦ 4."

af refine 1.6 --owner prover-1 --sibling -s "TRACE x=4: g_3(4)=4 (fixed) → g_1(4)=3 → g_3^{-1}(3)=2 → g_1^{-1}(2)=2 (fixed). Therefore 4 ↦ 2."

af refine 1.7 --owner prover-1 --sibling -s "TRACE x=5: g_3(5)=6 → g_1(6)=4 → g_3^{-1}(4)=4 (fixed) → g_1^{-1}(4)=6. Therefore 5 ↦ 6."

af refine 1.8 --owner prover-1 --sibling -s "TRACE x=6: g_3(6)=2 → g_1(2)=2 (fixed) → g_3^{-1}(2)=6 → g_1^{-1}(6)=1. Therefore 6 ↦ 1."

af refine 1.9 --owner prover-1 --sibling -s "TRACE x=7: g_3(7)=7 (fixed) → g_1(7)=1 → g_3^{-1}(1)=1 (fixed) → g_1^{-1}(1)=7. Therefore 7 ↦ 7 (FIXED POINT)."

# Add conclusion
af refine 1.10 --owner prover-1 --sibling -s "PART 3 - ORBIT ANALYSIS AND CONCLUSION:
Complete mapping: 1→5, 2→3, 3→4, 4→2, 5→6, 6→1, 7→7.
Orbit 1: 1→5→6→1 forms 3-cycle (1 5 6).
Orbit 2: 2→3→4→2 forms 3-cycle (2 3 4).
Orbit 3: 7→7 is fixed.
RESULT: [g_1, g_3] = (1 5 6)(2 3 4)."

# Release for verification
af release 1 --owner prover-1
```

### Step 4: Spawn Parallel Pedantic Verifiers

Spawn 3-4 verifier agents in parallel to check different parts:

**Verifier 1:** Check nodes 1.1, 1.2 (inverses and action tables)
**Verifier 2:** Check nodes 1.3, 1.4, 1.5, 1.6 (traces for x=1,2,3,4)
**Verifier 3:** Check nodes 1.7, 1.8, 1.9, 1.10 (traces for x=5,6,7 and conclusion)

Each verifier should:
```bash
# For each assigned node:
af claim <node> --owner pedantic-verifier-N --role verifier

# Verify independently by recomputing
# If correct:
af accept <node> --agent pedantic-verifier-N

# If incorrect:
af challenge <node> --owner pedantic-verifier-N --target inference --severity critical --reason "<detailed reason>"

# Release:
af release <node> --owner pedantic-verifier-N
```

### Step 5: Final Verification and Acceptance

Once all child nodes are validated:

```bash
# Final verifier accepts root
af claim 1 --owner final-verifier --role verifier
af accept 1 --agent final-verifier --confirm
af release 1 --owner final-verifier

# Verify completion
af status
```

Expected final state: All nodes `validated` and `clean`.

---

## Definitions Summary

| Definition | Content |
|------------|---------|
| `Domain_S7` | S_7 acts on {1, 2, 3, 4, 5, 6, 7} |
| `g_1` | g_1 = (1 6 4 3 7), a 5-cycle; 1→6→4→3→7→1; fixes 2, 5 |
| `g_3` | g_3 = (5 6 2 3), a 4-cycle; 5→6→2→3→5; fixes 1, 4, 7 |
| `g_1_inv` | g_1^{-1} = (1 7 3 4 6); 1→7→3→4→6→1; fixes 2, 5 |
| `g_3_inv` | g_3^{-1} = (5 3 2 6); 5→3→2→6→5; fixes 1, 4, 7 |
| `Commutator` | [σ, τ] := σ^{-1} τ^{-1} σ τ; evaluated as σ^{-1}(τ^{-1}(σ(τ(x)))) |
| `Cycle_Multiplication` | σ · τ means apply τ first, then σ |
| `Cycle_Inverse` | Inverse of (a_1 ... a_ℓ) is (a_ℓ ... a_1) |

---

## af Command Quick Reference

```bash
# Status and inspection
af status                    # View proof tree
af defs                      # List all definitions
af def <name>                # View specific definition
af challenges                # List all challenges

# Adding definitions
af def-add <name> "<content>"

# Prover workflow
af claim <node> --owner <id> --role prover
af refine <node> --owner <id> -s "<statement>"
af refine <node> --owner <id> --sibling -s "<statement>"
af release <node> --owner <id>

# Verifier workflow
af claim <node> --owner <id> --role verifier
af challenge <node> --owner <id> --target <target> --severity <severity> --reason "<reason>"
af accept <node> --agent <id> [--confirm]
af release <node> --owner <id>

# Challenge resolution
af resolve-challenge <challenge-id> --owner <id> --response "<response>"

# Challenge targets: statement, inference, dependencies, gap, domain, scope, context, type_error, completeness
# Challenge severities: critical (blocks), major (blocks), minor, note
```

---

## Expected Proof Structure

```
1 [root] [g_1, g_3] = (1 5 6)(2 3 4)
├── 1.1 [overview] Proof via direct cycle multiplication
├── 1.2 Inverse verification: g_1^{-1} = (1 7 3 4 6), g_3^{-1} = (5 3 2 6)
├── 1.3 Action tables for all four permutations
├── 1.4 TRACE x=1: 1 → 5
├── 1.5 TRACE x=2: 2 → 3
├── 1.6 TRACE x=3: 3 → 4
├── 1.7 TRACE x=4: 4 → 2
├── 1.8 TRACE x=5: 5 → 6
├── 1.9 TRACE x=6: 6 → 1
├── 1.10 TRACE x=7: 7 → 7 (fixed)
└── 1.11 Orbit analysis: (1 5 6)(2 3 4)
```

---

## Checklist Before Starting

- [ ] Navigate to `./lemmas/lemma07_commutator_g1g3/`
- [ ] Run `af status` to see current state
- [ ] Run `af defs` to confirm no existing definitions
- [ ] Add ALL 8 definitions before writing proof
- [ ] Compute inverses correctly using cycle reversal
- [ ] Trace EACH of the 7 elements step by step
- [ ] Verify the final cycle decomposition matches (1 5 6)(2 3 4)
- [ ] Spawn parallel verifier agents (don't verify inline)
- [ ] Resolve all challenges before final acceptance
- [ ] Ensure all nodes are `validated` AND `clean` before declaring complete

---

## Context and References

- **Master document:** `./proof_master.md` (Lemma 7 at lines 173-211, Version 2.0 corrected)
- **Previous lemmas:**
  - `./lemmas/lemma01_block_preservation/` - VALIDATED
  - `./lemmas/lemma02_induced_action/` - VALIDATED
  - `./lemmas/lemma03_base_case_structure/` - VALIDATED
  - `./lemmas/lemma04_base_case_exclusion/` - VALIDATED
  - `./lemmas/lemma05_transitivity/` - VALIDATED
  - `./lemmas/lemma06_commutator_g1g2/` - REFUTED (original claim wrong, correct result: (1 7 5)(2 4 6))
- **This handoff:** `./HANDOFF_LEMMA07.md`
- **Previous handoff:** `./HANDOFF_LEMMA06.md` (note: contains outdated info from before corrections)

---

## Why This Lemma Matters

Lemma 7 is part of **Part III: Commutator Computations** (Lemmas 6-9). These lemmas work together to produce an explicit 3-cycle in H:

1. **Lemma 6:** [g₁, g₂] = (1 7 5)(2 4 6) — c₁₂
2. **Lemma 7:** [g₁, g₃] = (1 5 6)(2 3 4) — c₁₃ ← **THIS LEMMA**
3. **Lemma 8:** [g₂, g₃] = (1 6 2)(3 5 4)
4. **Lemma 9:** (c₁₂ · c₁₃⁻¹)² = (1 6 2) — a single 3-cycle!

The extraction in Lemma 9 works as follows:
- c₁₂ · c₁₃⁻¹ = (1 2 6)(3 4)(5 7)
- Squaring eliminates the transpositions: (c₁₂ · c₁₃⁻¹)² = (1 6 2)

Having an explicit 3-cycle is crucial for applying **Jordan's Theorem** (Lemma 12), which states that a primitive group containing a 3-cycle must contain A_n.

---

## Differences from Lemma 06

| Aspect | Lemma 06 | Lemma 07 |
|--------|----------|----------|
| Generators | g₁, g₂ | g₁, g₃ |
| Second generator | (1 2 4 5) — 4-cycle | (5 6 2 3) — 4-cycle |
| Fixed points | 3 fixed by commutator | 7 fixed by commutator |
| Result | (1 7 5)(2 4 6) | (1 5 6)(2 3 4) |

The computation structure is identical; only the specific generators differ.

---

## Common Pitfalls

1. **Wrong inverse for g₃:** Make sure g₃⁻¹ = (5 3 2 6), NOT (3 2 6 5) or other forms.

2. **Forgetting fixed points:** When g₃(1) = 1, don't skip the step — explicitly note "1 is fixed by g₃".

3. **Order of composition:** Always apply right-to-left: g₃ first, then g₁, then g₃⁻¹, then g₁⁻¹.

4. **Mixing up g₂ and g₃:** This lemma uses g₁ and g₃, NOT g₂. Double-check the generators.

---

Good luck! The adversarial framework will catch any computational errors, so focus on clarity and completeness rather than speed.
