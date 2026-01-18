# Handoff: Proving Lemma 04 (Base Case Exclusion)

## Overview

This document provides detailed guidance for the next agent proving Lemma 04 using the `af` (Adversarial Proof Framework) tool.

**Lemma 04 Location:** `./lemmas/lemma04_base_case_exclusion/`

**Lemma 04 Statement:** |H_6| = 24 < 360 = |A_6|, hence H_6 ∉ {A_6, S_6}.

**Dependencies:** Lemma 3 (Structure of Base Case Group)

**Reference:** See `./proof_master.md` for the complete proof structure and all lemma statements.

---

## Proof Chain So Far

The following lemmas have been validated and can be cited as dependencies:

| Lemma | Location | Statement | Status |
|-------|----------|-----------|--------|
| **Lemma 1** | `lemma01_block_preservation/` | B₀ = {{1,4}, {2,5}, {3,6}} is preserved setwise by h₁, h₂, h₃ | VALIDATED |
| **Lemma 2** | `lemma02_induced_action/` | φ: H_6 → S_{B₀} satisfies Im(φ) = S_3 | VALIDATED |
| **Lemma 3** | `lemma03_base_case_structure/` | H_6 ≅ S_4, acting imprimitively on {1,...,6} | VALIDATED |

**Key result from Lemma 3:** |H_6| = 24 = |S_4|

---

## Lessons Learned from Previous Lemmas

### Critical Success Factors

1. **Spawn parallel verifier agents** - Use `Task` tool with `subagent_type="general-purpose"` to spawn multiple pedantic verifiers in parallel. Never verify inline.

2. **Add definitions FIRST** - Before any proof work, add all necessary definitions using `af def-add`. Verifiers challenge every undefined term.

3. **Cite previous lemmas explicitly** - When referencing Lemma 3, explain it is a validated external result from `lemma03_base_case_structure`.

4. **Iterative refinement** - Expect multiple rounds:
   - Prover writes proof → Verifiers challenge → Prover resolves → Verifiers re-verify → Accept

### Common Challenges to Anticipate

| Challenge Type | Example | Resolution |
|----------------|---------|------------|
| Undefined reference | "Lemma 3 not defined" | Cite as external dependency from `lemma03_base_case_structure` |
| Missing justification | "Why is |A_6| = 360?" | |A_6| = 6!/2 = 720/2 = 360 (standard formula) |
| Missing justification | "Why is |S_6| = 720?" | |S_6| = 6! = 720 (definition of symmetric group) |
| Logical gap | "How does |H_6| < |A_6| imply H_6 ≠ A_6?" | Subgroup equality requires same cardinality |

---

## Proof Strategy for Lemma 04

This is a straightforward lemma. The proof has three parts:
1. |H_6| = 24 (from Lemma 3)
2. |A_6| = 360 and |S_6| = 720
3. 24 < 360 < 720, so H_6 cannot equal A_6 or S_6

### Step 1: Navigate and Check Status

```bash
cd /home/tobiasosborne/Projects/af-tests/examples/lemmas/lemma04_base_case_exclusion

# Check current state
af status

# Check existing definitions (should be empty)
af defs
```

### Step 2: Add All Required Definitions

```bash
# Domain definition
af def-add Domain "Ω = {1, 2, 3, 4, 5, 6}, the finite set on which all permutations act."

# The group H_6
af def-add H_6 "H_6 = ⟨h₁, h₂, h₃⟩ ≤ Sym(Ω), where h₁ = (1 6 4 3), h₂ = (1 2 4 5), h₃ = (5 6 2 3)."

# Symmetric group S_6
af def-add S_6 "S_6 = Sym(Ω) is the symmetric group on 6 elements, with |S_6| = 6! = 720."

# Alternating group A_6
af def-add A_6 "A_6 is the alternating group on 6 elements, consisting of all even permutations in S_6. |A_6| = 6!/2 = 360."

# S_4 for reference
af def-add S_4 "S_4 is the symmetric group on 4 elements, with |S_4| = 4! = 24."

# Factorial formula
af def-add Factorial "For n ∈ ℕ, n! = n × (n-1) × ... × 2 × 1. In particular: 4! = 24, 6! = 720."

# Subgroup cardinality principle
af def-add Subgroup_Cardinality "If H ≤ G are groups and H = G, then |H| = |G|. Equivalently, if |H| ≠ |G|, then H ≠ G."
```

### Step 3: Claim and Refine as Prover

```bash
# Claim root node
af claim 1 --owner prover-1 --role prover

# Refine with overview
af refine 1 --owner prover-1 -s "We show H_6 ∉ {A_6, S_6} by comparing cardinalities. By Lemma 3, |H_6| = 24. By definition, |A_6| = 360 and |S_6| = 720. Since 24 < 360 < 720, and subgroup equality requires equal cardinality, H_6 cannot equal A_6 or S_6."

# Add node for |H_6| = 24
af refine 1.1 --owner prover-1 --sibling -s "Part 1: |H_6| = 24.
By Lemma 3 (Structure of Base Case Group, validated in lemma03_base_case_structure), H_6 ≅ S_4.
Therefore |H_6| = |S_4| = 4! = 24."

# Add node for |A_6| and |S_6|
af refine 1.2 --owner prover-1 --sibling -s "Part 2: |A_6| = 360 and |S_6| = 720.
By definition of the symmetric group, |S_6| = 6! = 720.
By definition of the alternating group, |A_6| = |S_6|/2 = 360.
(The alternating group consists of even permutations, exactly half of S_n.)"

# Add node for the comparison and conclusion
af refine 1.3 --owner prover-1 --sibling -s "Part 3: H_6 ∉ {A_6, S_6}.
We have: |H_6| = 24, |A_6| = 360, |S_6| = 720.
Since 24 < 360 < 720, and subgroup equality requires |H| = |G| (by Subgroup_Cardinality),
we conclude H_6 ≠ A_6 and H_6 ≠ S_6.
Therefore H_6 ∉ {A_6, S_6}."

# Release the claim
af release 1 --owner prover-1
```

### Step 4: Spawn Parallel Pedantic Verifiers

Spawn 3 verifier agents in parallel (one for each child node 1.1, 1.2, 1.3):

```
For each verifier agent:
1. af claim <node> --owner pedantic-verifier-N --role verifier
2. Check all definitions are properly cited
3. Verify mathematical calculations
4. Challenge any issues: af challenge <node> --owner pedantic-verifier-N --target <target> --severity <severity> --reason "<reason>"
5. If sound, accept: af accept <node> --agent pedantic-verifier-N
6. Release: af release <node> --owner pedantic-verifier-N
```

### Step 5: Resolve Challenges

Likely challenges and responses:

| Challenge | Response |
|-----------|----------|
| "Lemma 3 not in system" | "Lemma 3 is a validated external result from lemma03_base_case_structure. It establishes H_6 ≅ S_4, hence \|H_6\| = 24." |
| "Why does H_6 ≅ S_4 imply \|H_6\| = 24?" | "Isomorphic groups have the same cardinality. \|S_4\| = 4! = 24 by definition." |
| "Subgroup_Cardinality not justified" | "This is a fundamental property: if H = G as sets, they have the same cardinality. The contrapositive: unequal cardinality implies distinct groups." |

```bash
# Resolve each challenge
af resolve-challenge <challenge-id> --owner prover-1 --response "<detailed response>"
```

### Step 6: Final Verification and Acceptance

After all challenges are resolved:

```bash
# For each remaining pending node:
af claim <node> --owner final-verifier --role verifier
af accept <node> --agent final-verifier --confirm
af release <node> --owner final-verifier

# Accept root node last (after all children are validated)
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
| `Domain` | Ω = {1, 2, 3, 4, 5, 6} |
| `H_6` | H_6 = ⟨h₁, h₂, h₃⟩ ≤ Sym(Ω) |
| `S_6` | S_6 = Sym(Ω), \|S_6\| = 6! = 720 |
| `A_6` | A_6 = alternating group, \|A_6\| = 360 |
| `S_4` | S_4 = symmetric group on 4 elements, \|S_4\| = 24 |
| `Factorial` | n! formula, 4! = 24, 6! = 720 |
| `Subgroup_Cardinality` | H = G implies \|H\| = \|G\| |

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
1 [root] |H_6| = 24 < 360 = |A_6|, hence H_6 ∉ {A_6, S_6}
├── 1.1 [overview] Proof strategy via cardinality comparison
├── 1.2 |H_6| = 24 (from Lemma 3)
├── 1.3 |A_6| = 360 and |S_6| = 720 (definitions)
└── 1.4 Conclusion: 24 < 360 < 720 implies H_6 ∉ {A_6, S_6}
```

---

## Checklist Before Starting

- [ ] Navigate to `./lemmas/lemma04_base_case_exclusion/`
- [ ] Run `af status` to see current state
- [ ] Run `af defs` to confirm no existing definitions
- [ ] Add ALL 7 definitions before writing proof
- [ ] Reference Lemma 3 explicitly (external dependency)
- [ ] Spawn parallel verifier agents (don't verify inline)
- [ ] Resolve all challenges before final acceptance
- [ ] Ensure all nodes are `validated` AND `clean` before declaring complete

---

## Context and References

- **Previous lemmas:**
  - `./lemmas/lemma01_block_preservation/` (validated)
  - `./lemmas/lemma02_induced_action/` (validated)
  - `./lemmas/lemma03_base_case_structure/` (validated)
- **Master document:** `./proof_master.md` (contains all lemma statements and proof sketches)
- **This handoff:** `./HANDOFF_LEMMA04.md`
- **Previous handoff:** `./HANDOFF_LEMMA02.md` (for reference on workflow)

---

## Why This Lemma Matters

Lemma 4 completes Part I of the proof (Base Case Analysis). It establishes that when n = k = m = 0 (the base case), the group H_6 is strictly smaller than both A_6 and S_6. This is crucial because:

1. The main theorem claims H = A_N or H = S_N for most parameter values
2. The base case n = k = m = 0 is an **exception** that must be excluded
3. Lemmas 1-4 together show: H_6 ≅ S_4 ⊊ A_6 ⊊ S_6

After Lemma 4, the proof moves to Part II (Transitivity) with Lemma 5.

Good luck!
