# Handoff: Proving Lemma 09 (3-Cycle Extraction)

## Overview

This document provides detailed guidance for the next agent proving Lemma 09 using the `af` (Adversarial Proof Framework) tool.

**Lemma 09 Location:** `./lemmas/lemma09_3cycle_extraction/`

**Lemma 09 Statement:** Let c₁₂ := [g₁, g₂] = (1 7 5)(2 4 6) and c₁₃ := [g₁, g₃] = (1 5 6)(2 3 4). Then:
1. c₁₂ · c₁₃⁻¹ = (1 2 6)(3 4)(5 7)
2. (c₁₂ · c₁₃⁻¹)² = (1 6 2), a 3-cycle in H.

**Dependencies:** Lemmas 6 and 7 (for the values of c₁₂ and c₁₃).

**Reference:** See `./proof_master.md` for the complete proof structure (Lemma 9 at lines 249-298, Version 2.0).

---

## CRITICAL: Root Claim Must Be Amended

The current root claim in the lemma09 directory is **WRONG** - it uses the old incorrect values:
- OLD (wrong): c₁₂ = (1 2 6)(3 4 5), c₁₃ = (2 4 6)(3 5 7)
- NEW (correct): c₁₂ = (1 7 5)(2 4 6), c₁₃ = (1 5 6)(2 3 4)

**You MUST amend the root claim before proving.** Use:
```bash
af claim 1 --owner prover-1 --role prover
af amend 1 --owner prover-1 --statement "Let c_12 := (1 7 5)(2 4 6) and c_13 := (1 5 6)(2 3 4). Then: (1) c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7), and (2) (c_12 * c_13^{-1})^2 = (1 6 2)."
```

---

## Proof Chain So Far

The following lemmas have been validated and provide the foundation for Lemma 9:

| Lemma | Location | Statement | Status |
|-------|----------|-----------|--------|
| **Lemma 1** | `lemma01_block_preservation/` | B₀ = {{1,4}, {2,5}, {3,6}} is preserved setwise by h₁, h₂, h₃ | VALIDATED |
| **Lemma 2** | `lemma02_induced_action/` | φ: H_6 → S_{B₀} satisfies Im(φ) = S_3 | VALIDATED |
| **Lemma 3** | `lemma03_base_case_structure/` | H_6 ≅ S_4, acting imprimitively on {1,...,6} | VALIDATED |
| **Lemma 4** | `lemma04_base_case_exclusion/` | \|H_6\| = 24 < 360 = \|A_6\|, hence H_6 ∉ {A_6, S_6} | VALIDATED |
| **Lemma 5** | `lemma05_transitivity/` | H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω | VALIDATED |
| **Lemma 6** | `lemma06_commutator_g1g2/` | [g₁, g₂] = (1 7 5)(2 4 6) | REFUTED (original wrong, computation verified) |
| **Lemma 7** | `lemma07_commutator_g1g3/` | [g₁, g₃] = (1 5 6)(2 3 4) | **VALIDATED** |
| **Lemma 8** | `lemma08_commutator_g2g3/` | [g₂, g₃] = (1 6 2)(3 5 4) | **VALIDATED** |

**Note:** Lemma 9 depends on Lemmas 6 and 7 for the values of c₁₂ and c₁₃.

---

## Lessons from Previous Lemmas

1. **The original proof_master.md had errors in ALL commutator computations** - they have been corrected in Version 2.0

2. **Spawn parallel verifier agents** - Use `Task` tool with `subagent_type="general-purpose"` to spawn multiple pedantic verifiers

3. **Add definitions FIRST** - Before any proof work, add all necessary definitions using `af def-add`

4. **Show ALL computation steps** - Trace each element explicitly in tables

5. **Amend root claims when needed** - Use `af amend` to fix incorrect initial statements

---

## Proof Strategy for Lemma 09

This lemma has three parts:

### Part 1: Compute c₁₃⁻¹

c₁₃ = (1 5 6)(2 3 4)

For 3-cycles: (a b c)⁻¹ = (a c b)

So: c₁₃⁻¹ = (1 6 5)(2 4 3)

### Part 2: Compute c₁₂ · c₁₃⁻¹

c₁₂ = (1 7 5)(2 4 6)
c₁₃⁻¹ = (1 6 5)(2 4 3)

Apply c₁₃⁻¹ first, then c₁₂:

| x | c₁₃⁻¹(x) | c₁₂(·) | Result |
|---|----------|--------|--------|
| 1 | 6 | 2 | 1 → 2 |
| 2 | 4 | 6 | 2 → 6 |
| 3 | 2 | 4 | 3 → 4 |
| 4 | 3 | 3 | 4 → 3 |
| 5 | 1 | 7 | 5 → 7 |
| 6 | 5 | 1 | 6 → 1 |
| 7 | 7 | 5 | 7 → 5 |

**Orbit analysis:**
- Orbit 1: 1 → 2 → 6 → 1 gives (1 2 6)
- Orbit 2: 3 → 4 → 3 gives (3 4)
- Orbit 3: 5 → 7 → 5 gives (5 7)

**Result:** c₁₂ · c₁₃⁻¹ = (1 2 6)(3 4)(5 7)

### Part 3: Compute (c₁₂ · c₁₃⁻¹)²

The element (1 2 6)(3 4)(5 7) is a product of disjoint cycles.

When squaring disjoint cycles:
- (1 2 6)² = (1 6 2) — 3-cycle squared gives 3-cycle
- (3 4)² = e — transposition squared gives identity
- (5 7)² = e — transposition squared gives identity

**Result:** (c₁₂ · c₁₃⁻¹)² = (1 6 2)

This is a **3-cycle in H**, which is crucial for applying Jordan's Theorem in Lemma 12.

---

## Step-by-Step Instructions

### Step 1: Navigate and Check Status

```bash
cd /home/tobiasosborne/Projects/af-tests/examples/lemmas/lemma09_3cycle_extraction

# Check current state
af status

# Check existing definitions (should be empty)
af defs
```

### Step 2: Amend the Root Claim

The current root claim is WRONG. Fix it:

```bash
# Claim root node
af claim 1 --owner prover-1 --role prover

# Amend to correct statement
af amend 1 --owner prover-1 --statement "Let c_12 := (1 7 5)(2 4 6) and c_13 := (1 5 6)(2 3 4). Then: (1) c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7), and (2) (c_12 * c_13^{-1})^2 = (1 6 2)."
```

### Step 3: Add All Required Definitions

```bash
# Domain
af def-add Domain_S7 "The symmetric group S_7 acts on {1, 2, 3, 4, 5, 6, 7}."

# Commutator c_12 from Lemma 6
af def-add c_12 "c_12 := [g_1, g_2] = (1 7 5)(2 4 6), a product of two disjoint 3-cycles. Computed in Lemma 6."

# Commutator c_13 from Lemma 7
af def-add c_13 "c_13 := [g_1, g_3] = (1 5 6)(2 3 4), a product of two disjoint 3-cycles. Computed in Lemma 7."

# Inverse of c_13
af def-add c_13_inv "c_13^{-1} = (1 6 5)(2 4 3). For 3-cycle (a b c), inverse is (a c b)."

# Cycle multiplication convention
af def-add Cycle_Multiplication "When computing σ · τ, we apply τ first, then σ. So (σ · τ)(x) = σ(τ(x))."

# Cycle inverse for 3-cycles
af def-add Three_Cycle_Inverse "For a 3-cycle (a b c), its inverse is (a c b). Equivalently, (a b c)^{-1} = (a c b)."

# Squaring disjoint cycles
af def-add Disjoint_Cycle_Power "For disjoint cycles σ = σ_1 σ_2 ... σ_k, we have σ^n = σ_1^n σ_2^n ... σ_k^n."

# Transposition squaring
af def-add Transposition_Square "For any transposition (a b), we have (a b)^2 = e (identity)."
```

### Step 4: Add Proof Structure

```bash
# Overview
af refine 1 --owner prover-1 -s "OVERVIEW: We compute c_12 * c_13^{-1} and then square it to extract a 3-cycle. The computation uses: c_12 = (1 7 5)(2 4 6) from Lemma 6, c_13 = (1 5 6)(2 3 4) from Lemma 7."

# Part 1: Compute c_13 inverse
af refine 1.1 --owner prover-1 --sibling -s "PART 1 - INVERSE OF c_13 (citing Three_Cycle_Inverse): c_13 = (1 5 6)(2 3 4). Each 3-cycle inverts by reversing: (1 5 6)^{-1} = (1 6 5), (2 3 4)^{-1} = (2 4 3). Thus c_13^{-1} = (1 6 5)(2 4 3)."

# Part 2: Action tables
af refine 1.2 --owner prover-1 --sibling -s "PART 2 - ACTION TABLES: c_12 = (1 7 5)(2 4 6): 1→7, 7→5, 5→1, 2→4, 4→6, 6→2; fixes 3. c_13^{-1} = (1 6 5)(2 4 3): 1→6, 6→5, 5→1, 2→4, 4→3, 3→2; fixes 7."

# Element traces for c_12 * c_13^{-1}
af refine 1.3 --owner prover-1 --sibling -s "TRACE x=1: c_13^{-1}(1)=6 → c_12(6)=2. Therefore 1 ↦ 2."

af refine 1.4 --owner prover-1 --sibling -s "TRACE x=2: c_13^{-1}(2)=4 → c_12(4)=6. Therefore 2 ↦ 6."

af refine 1.5 --owner prover-1 --sibling -s "TRACE x=3: c_13^{-1}(3)=2 → c_12(2)=4. Therefore 3 ↦ 4."

af refine 1.6 --owner prover-1 --sibling -s "TRACE x=4: c_13^{-1}(4)=3 → c_12(3)=3 (3 is fixed by c_12). Therefore 4 ↦ 3."

af refine 1.7 --owner prover-1 --sibling -s "TRACE x=5: c_13^{-1}(5)=1 → c_12(1)=7. Therefore 5 ↦ 7."

af refine 1.8 --owner prover-1 --sibling -s "TRACE x=6: c_13^{-1}(6)=5 → c_12(5)=1. Therefore 6 ↦ 1."

af refine 1.9 --owner prover-1 --sibling -s "TRACE x=7: c_13^{-1}(7)=7 (7 is fixed by c_13^{-1}) → c_12(7)=5. Therefore 7 ↦ 5."
```

Then claim node 1.9 and add the conclusion:

```bash
af claim 1.9 --owner prover-1 --role prover
af refine 1.9 --owner prover-1 -s "PART 3 - ORBIT ANALYSIS AND SQUARING: Complete mapping: 1→2, 2→6, 3→4, 4→3, 5→7, 6→1, 7→5. Orbits: (1 2 6), (3 4), (5 7). So c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7). Squaring: (1 2 6)^2 = (1 6 2), (3 4)^2 = e, (5 7)^2 = e. By Disjoint_Cycle_Power: (c_12 * c_13^{-1})^2 = (1 6 2). QED."

af release 1.9 --owner prover-1
af release 1 --owner prover-1
```

### Step 5: Spawn Parallel Pedantic Verifiers

Spawn 3 verifier agents in parallel to check different parts:

**Verifier 1:** Check nodes 1.1, 1.2 (inverses and action tables)
**Verifier 2:** Check nodes 1.3, 1.4, 1.5, 1.6 (traces for x=1,2,3,4)
**Verifier 3:** Check nodes 1.7, 1.8, 1.9, 1.9.1 (traces for x=5,6,7 and conclusion)

### Step 6: Final Verification and Acceptance

Once all child nodes are validated:

```bash
af claim 1 --owner final-verifier --role verifier
af accept 1 --agent final-verifier --confirm
af release 1 --owner final-verifier

# Verify completion
af status
```

---

## Definitions Summary

| Definition | Content |
|------------|---------|
| `Domain_S7` | S_7 acts on {1, 2, 3, 4, 5, 6, 7} |
| `c_12` | c_12 = [g_1, g_2] = (1 7 5)(2 4 6) from Lemma 6 |
| `c_13` | c_13 = [g_1, g_3] = (1 5 6)(2 3 4) from Lemma 7 |
| `c_13_inv` | c_13^{-1} = (1 6 5)(2 4 3) |
| `Cycle_Multiplication` | σ · τ means apply τ first, then σ |
| `Three_Cycle_Inverse` | (a b c)^{-1} = (a c b) |
| `Disjoint_Cycle_Power` | (σ_1 ... σ_k)^n = σ_1^n ... σ_k^n for disjoint cycles |
| `Transposition_Square` | (a b)² = e |

---

## Expected Proof Structure

```
1 [root] c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7) and (c_12 * c_13^{-1})² = (1 6 2)
├── 1.1 [overview] Proof via direct cycle multiplication
├── 1.2 PART 1: c_13^{-1} = (1 6 5)(2 4 3)
├── 1.3 PART 2: Action tables for c_12 and c_13^{-1}
├── 1.4 TRACE x=1: 1 → 2
├── 1.5 TRACE x=2: 2 → 6
├── 1.6 TRACE x=3: 3 → 4
├── 1.7 TRACE x=4: 4 → 3
├── 1.8 TRACE x=5: 5 → 7
├── 1.9 TRACE x=6: 6 → 1
├── 1.10 TRACE x=7: 7 → 5
└── 1.10.1 PART 3: Orbit analysis → (1 2 6)(3 4)(5 7), squaring → (1 6 2)
```

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
af amend <node> --owner <id> --statement "<new statement>"
af refine <node> --owner <id> -s "<statement>"
af refine <node> --owner <id> --sibling -s "<statement>"
af release <node> --owner <id>

# Verifier workflow
af claim <node> --owner <id> --role verifier
af challenge <node> --owner <id> --target <target> --severity <severity> --reason "<reason>"
af accept <node> --agent <id> [--confirm]
af release <node> --owner <id>

# Challenge targets: statement, inference, dependencies, gap, domain, scope, context, type_error, completeness
# Challenge severities: critical (blocks), major (blocks), minor, note
```

---

## Why This Lemma Matters

Lemma 9 is the culmination of **Part III: Commutator Computations**. It produces an explicit 3-cycle (1 6 2) in H.

This 3-cycle is essential for **Lemma 12 (Jordan's Theorem)**, which states:
> Let G ≤ Sₙ be primitive with n ≥ 5. If G contains a 3-cycle, then G ≥ Aₙ.

Combined with:
- **Lemma 5:** H is transitive
- **Lemma 11:** H is primitive (for n+k+m ≥ 1)
- **Lemma 9:** H contains a 3-cycle

We can conclude H ≥ Aₙ, which is the key step in the main theorem.

---

## Common Pitfalls

1. **Using wrong c₁₂ or c₁₃ values:** The original proof_master.md had errors. Use:
   - c₁₂ = (1 7 5)(2 4 6) — NOT (1 2 6)(3 4 5)
   - c₁₃ = (1 5 6)(2 3 4) — NOT (2 4 6)(3 5 7)

2. **Wrong inverse for c₁₃:** For 3-cycle (1 5 6), inverse is (1 6 5), NOT (6 5 1)

3. **Composition order:** For c₁₂ · c₁₃⁻¹, apply c₁₃⁻¹ first, then c₁₂

4. **Forgetting fixed points:** When c₁₂(3) = 3 (3 is fixed), note this explicitly

5. **Squaring 3-cycles:** (1 2 6)² = (1 6 2), NOT (1 2 6) or identity

---

## Context and References

- **Master document:** `./proof_master.md` (Lemma 9 at lines 249-298, Version 2.0 corrected)
- **Previous lemmas:**
  - `./lemmas/lemma06_commutator_g1g2/` - REFUTED (original claim wrong, correct result verified: (1 7 5)(2 4 6))
  - `./lemmas/lemma07_commutator_g1g3/` - VALIDATED: (1 5 6)(2 3 4)
  - `./lemmas/lemma08_commutator_g2g3/` - VALIDATED: (1 6 2)(3 5 4)
- **This handoff:** `./HANDOFF_LEMMA09.md`
- **Previous handoffs:** `./HANDOFF_LEMMA06.md`, `./HANDOFF_LEMMA07.md`

---

## Checklist Before Starting

- [ ] Navigate to `./lemmas/lemma09_3cycle_extraction/`
- [ ] Run `af status` to see current state
- [ ] **AMEND the root claim** — it has WRONG values from old proof_master
- [ ] Run `af defs` to confirm no existing definitions
- [ ] Add ALL 8 definitions before writing proof
- [ ] Verify c₁₃⁻¹ = (1 6 5)(2 4 3)
- [ ] Trace EACH of the 7 elements through c₁₂ · c₁₃⁻¹
- [ ] Verify the product is (1 2 6)(3 4)(5 7)
- [ ] Verify (1 2 6)² = (1 6 2) and transpositions square to identity
- [ ] Confirm final result is (1 6 2)
- [ ] Spawn parallel verifier agents (don't verify inline)
- [ ] Resolve all challenges before final acceptance
- [ ] Ensure all nodes are `validated` AND `clean` before declaring complete

---

Good luck! The adversarial framework will catch any computational errors, so focus on clarity and completeness rather than speed.
