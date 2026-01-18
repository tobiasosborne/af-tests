# Handoff: Proving Lemma 02 (Induced Action on Blocks)

## Overview

This document provides detailed guidance for the next agent proving Lemma 02 using the `af` (Adversarial Proof Framework) tool.

**Lemma 02 Location:** `./lemmas/lemma02_induced_action/`

**Lemma 02 Statement:** The map φ: H_6 → S_{B_0} induced by the action on blocks satisfies:
1. φ(h_1) = ({1,4} {3,6})
2. φ(h_2) = ({1,4} {2,5})
3. φ(h_3) = ({2,5} {3,6})

**Corollary:** Im(φ) = S_3

**Dependencies:** Lemma 1 (Block Preservation)

---

## Lessons Learned from Lemma 01

### What Worked

1. **Spawn parallel verifier agents** - Don't verify inline. Use `Task` tool with `subagent_type="general-purpose"` to spawn multiple pedantic verifiers in parallel.

2. **Add definitions FIRST** - Before any proof work, add all necessary definitions using `af def-add`. The verifiers will challenge every undefined term.

3. **Be maximally explicit** - Pedantic verifiers challenge:
   - Undefined notation (cycle notation, set action)
   - Missing domain specifications
   - Unjustified fixed points
   - Missing dependencies
   - Wrong inference types

4. **Iterative refinement** - Expect multiple rounds:
   - Prover writes proof → Verifiers challenge → Prover resolves → Verifiers re-challenge → Repeat until accepted

### Definitions Already Established (in lemma01)

These definitions were created for Lemma 1 and the SAME concepts apply to Lemma 2. You'll need to add similar definitions to the lemma02 workspace:

| Definition | Content |
|------------|---------|
| `Domain` | Ω = {1, 2, 3, 4, 5, 6} |
| `Cycle_Notation` | (a₁ a₂ ... aₖ) means σ(aᵢ) = aᵢ₊₁, σ(aₖ) = a₁ |
| `Fixed_Points` | Elements not in a cycle are fixed |
| `Set_Action` | σ(S) := {σ(x) : x ∈ S} |
| `Preserved_Setwise` | P preserved by σ iff ∀B ∈ P, σ(B) ∈ P |
| `Partition_B0` | B₀ = {{1,4}, {2,5}, {3,6}} |
| `Permutations_4cycles` | h₁ = (1 6 4 3), h₂ = (1 2 4 5), h₃ = (5 6 2 3) |

### New Definitions Needed for Lemma 02

| Definition | Content |
|------------|---------|
| `Induced_Action` | φ: Sym(Ω) → Sym(B₀) where φ(σ)(B) = σ(B) for B ∈ B₀ |
| `H_6` | H_6 = ⟨h₁, h₂, h₃⟩ ≤ Sym(Ω) |
| `S_B0` | S_{B_0} ≅ S_3, the symmetric group on the 3 blocks |
| `Block_Transposition` | A transposition in S_{B_0} swapping two blocks |

---

## Proof Strategy for Lemma 02

### Step 1: Initialize and Add Definitions

```bash
cd /home/tobiasosborne/Projects/af-tests/examples/lemmas/lemma02_induced_action

# Check current state
af status

# Add all necessary definitions
af def-add Domain "Ω = {1, 2, 3, 4, 5, 6}, the finite set on which all permutations act."

af def-add Cycle_Notation "The cycle (a₁ a₂ ... aₖ) denotes the permutation σ where σ(aᵢ) = aᵢ₊₁ for i < k, and σ(aₖ) = a₁. Elements not appearing in the cycle are fixed."

af def-add Partition_B0 "B₀ = {{1,4}, {2,5}, {3,6}}, a partition of Ω into three blocks of size 2."

af def-add Permutations_h1_h2_h3 "h₁ = (1 6 4 3), h₂ = (1 2 4 5), h₃ = (5 6 2 3) are 4-cycles in Sym(Ω). Explicit mappings:
h₁: 1→6→4→3→1, fixes {2,5}
h₂: 1→2→4→5→1, fixes {3,6}
h₃: 5→6→2→3→5, fixes {1,4}"

af def-add Set_Action "For σ ∈ Sym(Ω) and S ⊆ Ω, define σ(S) := {σ(x) : x ∈ S}."

af def-add Induced_Action "The induced action φ: Sym(Ω) → Sym(B₀) is defined by φ(σ)(B) = σ(B) for each block B ∈ B₀. This is well-defined when σ preserves B₀ setwise."

af def-add Block_Labeling "For convenience, label the blocks: B₁ = {1,4}, B₂ = {2,5}, B₃ = {3,6}. Then S_{B₀} ≅ S_3 acts on {B₁, B₂, B₃}."
```

### Step 2: Claim and Refine as Prover

```bash
# Claim root node
af claim 1 --owner prover-1 --role prover

# Add proof structure - the key insight is reading off from Lemma 1 results
af refine 1 --owner prover-1 -s "By Lemma 1, each hᵢ permutes B₀. The induced action φ(hᵢ) is determined by how hᵢ permutes the blocks. We read off from Lemma 1:
- h₁: {1,4}→{3,6}, {2,5}→{2,5}, {3,6}→{1,4}, so φ(h₁) swaps B₁↔B₃, fixes B₂
- h₂: {1,4}→{2,5}, {2,5}→{1,4}, {3,6}→{3,6}, so φ(h₂) swaps B₁↔B₂, fixes B₃
- h₃: {1,4}→{1,4}, {2,5}→{3,6}, {3,6}→{2,5}, so φ(h₃) swaps B₂↔B₃, fixes B₁"

# Add Part 1: φ(h₁)
af refine 1.1 --owner prover-1 --sibling -s "Part 1: Computing φ(h₁).
From Lemma 1, h₁ maps: {1,4}→{3,6}, {2,5}→{2,5}, {3,6}→{1,4}.
In block notation: B₁→B₃, B₂→B₂, B₃→B₁.
Therefore φ(h₁) = (B₁ B₃) = ({1,4} {3,6}), a transposition in S_{B₀}."

# Add Part 2: φ(h₂)
af refine 1.2 --owner prover-1 --sibling -s "Part 2: Computing φ(h₂).
From Lemma 1, h₂ maps: {1,4}→{2,5}, {2,5}→{1,4}, {3,6}→{3,6}.
In block notation: B₁→B₂, B₂→B₁, B₃→B₃.
Therefore φ(h₂) = (B₁ B₂) = ({1,4} {2,5}), a transposition in S_{B₀}."

# Add Part 3: φ(h₃)
af refine 1.3 --owner prover-1 --sibling -s "Part 3: Computing φ(h₃).
From Lemma 1, h₃ maps: {1,4}→{1,4}, {2,5}→{3,6}, {3,6}→{2,5}.
In block notation: B₁→B₁, B₂→B₃, B₃→B₂.
Therefore φ(h₃) = (B₂ B₃) = ({2,5} {3,6}), a transposition in S_{B₀}."

# Add Corollary: Im(φ) = S_3
af refine 1.4 --owner prover-1 --sibling -s "Corollary: Im(φ) = S_3.
The three transpositions (B₁ B₃), (B₁ B₂), (B₂ B₃) generate S_3.
Proof: S_3 is generated by any two distinct transpositions. Here we have all three transpositions (12), (13), (23) in S_3 notation.
Therefore Im(φ) = ⟨φ(h₁), φ(h₂), φ(h₃)⟩ = S_3."

# Release
af release 1 --owner prover-1
```

### Step 3: Spawn Pedantic Verifiers

Use parallel Task agents to verify each node:

```python
# Spawn 4 verifiers in parallel for nodes 1.1, 1.2, 1.3, 1.4
# Each verifier should:
# 1. af claim <node> --owner pedantic-verifier-N --role verifier
# 2. Scrutinize for: undefined terms, missing justifications, logical gaps
# 3. Challenge using: af challenge <node> --owner pedantic-verifier-N --target <target> --severity <severity> --reason "<reason>"
# 4. af release <node> --owner pedantic-verifier-N
```

### Step 4: Address Challenges

Expect challenges like:
- "Induced_Action not defined" → cite the definition
- "How does Lemma 1 justify this?" → add explicit reference/dependency
- "Why do transpositions generate S_3?" → cite standard group theory result
- "Block labeling convention not stated" → cite Block_Labeling definition

Resolve each challenge:
```bash
af resolve-challenge <challenge-id> --owner prover-1 --response "<detailed response citing definitions>"
```

### Step 5: Re-verify and Accept

After resolving all challenges, spawn verifiers again to accept:
```bash
af claim <node> --owner final-verifier --role verifier
af accept <node> --agent final-verifier
af release <node> --owner final-verifier
```

---

## Key Differences from Lemma 01

| Aspect | Lemma 01 | Lemma 02 |
|--------|----------|----------|
| Focus | Block preservation (computational) | Induced homomorphism (structural) |
| Main work | Computing σ(B) for each block | Reading off permutation in S_3 |
| Key definition | Set_Action | Induced_Action |
| Dependency | None | Lemma 1 |
| Corollary | None | Im(φ) = S_3 |

---

## Expected Challenges and Responses

| Challenge Type | Example | Response |
|----------------|---------|----------|
| Undefined Induced_Action | "φ is never defined" | Cite Induced_Action definition |
| Missing Lemma 1 reference | "Where does the block mapping come from?" | "Established in Lemma 1, node 1.2/1.3/1.4" |
| Unjustified S_3 generation | "Why do these transpositions generate S_3?" | "Standard result: S_n is generated by any (n-1) transpositions forming a connected graph on n vertices. Here (12), (13), (23) form a complete graph on 3 vertices." |
| Type mismatch | "φ(h₁) should be in Sym(B₀), not S_3" | "S_{B₀} ≅ S_3 via the Block_Labeling bijection B₁↔1, B₂↔2, B₃↔3" |

---

## af Command Reference

```bash
# View status
af status

# Add definition
af def-add <name> "<content>"

# List definitions
af defs

# View definition
af def <name>

# Claim node (prover)
af claim <node> --owner <agent-id> --role prover

# Claim node (verifier)
af claim <node> --owner <agent-id> --role verifier

# Refine (add child)
af refine <node> --owner <agent-id> -s "<statement>"

# Refine (add sibling)
af refine <node> --owner <agent-id> --sibling -s "<statement>"

# Release claim
af release <node> --owner <agent-id>

# Challenge (verifier)
af challenge <node> --owner <agent-id> --target <target> --severity <severity> --reason "<reason>"

# Targets: statement, inference, dependencies, gap, domain, scope, context, type_error, completeness
# Severities: critical, major, minor, note

# Resolve challenge (prover)
af resolve-challenge <challenge-id> --owner <agent-id> --response "<response>"

# Accept (verifier)
af accept <node> --agent <agent-id>

# List challenges
af challenges

# List jobs
af jobs
```

---

## Checklist Before Starting

- [ ] Navigate to `./lemmas/lemma02_induced_action/`
- [ ] Run `af status` to see current state
- [ ] Add ALL definitions before writing proof
- [ ] Reference Lemma 1 results explicitly
- [ ] Spawn parallel verifier agents (don't verify inline)
- [ ] Expect 2-3 rounds of challenge/resolution
- [ ] Ensure all nodes are validated AND clean before declaring complete

---

## Contact / Context

- **Previous lemma:** `./lemmas/lemma01_block_preservation/` (fully validated)
- **Master document:** `./proof_master.md` (contains all lemma statements)
- **This handoff:** `./HANDOFF_LEMMA02.md`

Good luck!
