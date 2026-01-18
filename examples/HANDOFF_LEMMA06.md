# Handoff: Proving Lemma 06 (Commutator [g₁, g₂])

## Overview

This document provides detailed guidance for proving Lemma 06 using the `af` (Adversarial Proof Framework) tool.

**Lemma 06 Location:** `./lemmas/lemma06_commutator_g1g2/`

**Lemma 06 Statement:** Let g₁ = (1 6 4 3 7) and g₂ = (1 2 4 5) in S₇ (case n=1, k=m=0). Then [g₁, g₂] := g₁⁻¹ g₂⁻¹ g₁ g₂ = **(1 7 5)(2 4 6)**.

**Dependencies:** None (this is a direct computation).

**Reference:** See `./proof_master.md` for the complete proof structure (Lemma 6 at lines 132-169, Version 2.0).

---

## ⚠️ IMPORTANT: This Lemma Has Been Completed

**Status: REFUTED** — The adversarial proof process found that the **original claim was incorrect**.

- **Original (wrong) claim:** [g₁, g₂] = (1 2 6)(3 4 5)
- **Verified correct result:** [g₁, g₂] = **(1 7 5)(2 4 6)**

The proof_master.md has been updated to Version 2.0 with the corrected result. All 12 child nodes were **VALIDATED** with step-by-step verified computations. The root node was **REFUTED** because its original statement was mathematically false.

This is a successful outcome for the adversarial framework — it correctly identified an error in the original problem statement.

---

## Proof Chain So Far

| Lemma | Location | Statement | Status |
|-------|----------|-----------|--------|
| **Lemma 1** | `lemma01_block_preservation/` | B₀ = {{1,4}, {2,5}, {3,6}} is preserved setwise by h₁, h₂, h₃ | VALIDATED |
| **Lemma 2** | `lemma02_induced_action/` | φ: H_6 → S_{B₀} satisfies Im(φ) = S_3 | VALIDATED |
| **Lemma 3** | `lemma03_base_case_structure/` | H_6 ≅ S_4, acting imprimitively on {1,...,6} | VALIDATED |
| **Lemma 4** | `lemma04_base_case_exclusion/` | \|H_6\| = 24 < 360 = \|A_6\|, hence H_6 ∉ {A_6, S_6} | VALIDATED |
| **Lemma 5** | `lemma05_transitivity/` | H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω | VALIDATED |
| **Lemma 6** | `lemma06_commutator_g1g2/` | [g₁, g₂] = (1 7 5)(2 4 6) | **REFUTED** (original claim wrong) |
| **Lemma 7** | `lemma07_commutator_g1g3/` | [g₁, g₃] = (1 5 6)(2 3 4) | **VALIDATED** ✓ |
| **Lemma 8** | `lemma08_commutator_g2g3/` | [g₂, g₃] = (1 6 2)(3 5 4) | **VALIDATED** ✓ |
| **Lemma 9** | `lemma09_3cycle_extraction/` | (c₁₂ · c₁₃⁻¹)² = (1 6 2) | PENDING |

---

## Verified Computation

### Commutator Convention

**[σ, τ] := σ⁻¹ τ⁻¹ σ τ**

Evaluated as: [g₁, g₂](x) = g₁⁻¹(g₂⁻¹(g₁(g₂(x))))

### Action Tables

- **g₁ = (1 6 4 3 7):** 1→6→4→3→7→1; fixes 2, 5
- **g₂ = (1 2 4 5):** 1→2→4→5→1; fixes 3, 6, 7
- **g₁⁻¹ = (1 7 3 4 6):** 1→7→3→4→6→1; fixes 2, 5
- **g₂⁻¹ = (1 5 4 2):** 1→5→4→2→1; fixes 3, 6, 7

### Element Traces (Verified)

| x | g₂(x) | g₁(g₂(x)) | g₂⁻¹(...) | g₁⁻¹(...) | Result |
|---|-------|-----------|-----------|-----------|--------|
| 1 | 2 | 2 | 1 | 7 | 1 → 7 |
| 2 | 4 | 3 | 3 | 4 | 2 → 4 |
| 3 | 3 | 7 | 7 | 3 | 3 → 3 (fixed) |
| 4 | 5 | 5 | 4 | 6 | 4 → 6 |
| 5 | 1 | 6 | 6 | 1 | 5 → 1 |
| 6 | 6 | 4 | 2 | 2 | 6 → 2 |
| 7 | 7 | 1 | 5 | 5 | 7 → 5 |

### Orbit Analysis

- **Orbit 1:** 1 → 7 → 5 → 1 gives **(1 7 5)**
- **Orbit 2:** 2 → 4 → 6 → 2 gives **(2 4 6)**
- **Fixed:** 3

### Result

**[g₁, g₂] = (1 7 5)(2 4 6)**

---

## Lessons Learned

1. **Never trust pre-computed results** — Always verify step-by-step
2. **The adversarial framework works** — It correctly identified the computational error
3. **Use element trace tables** — Makes verification easy and errors obvious
4. **Spawn parallel verifiers** — Independent verification catches mistakes

---

## Next Steps

**Lemmas 7 and 8 have been completed.** Proceed to **Lemma 09**: See `./HANDOFF_LEMMA09.md`

The corrected Lemma 6 result (c₁₂ = (1 7 5)(2 4 6)) is used in Lemma 9 to extract a 3-cycle:
- c₁₂ = [g₁, g₂] = (1 7 5)(2 4 6) — from Lemma 6
- c₁₃ = [g₁, g₃] = (1 5 6)(2 3 4) — from Lemma 7
- (c₁₂ · c₁₃⁻¹)² = (1 6 2) — the 3-cycle needed for Jordan's Theorem

---

## af Command Quick Reference

```bash
# Status and inspection
af status                    # View proof tree
af defs                      # List all definitions
af challenges                # List all challenges

# Adding definitions
af def-add <name> "<content>"

# Prover workflow
af claim <node> --owner <id> --role prover
af refine <node> --owner <id> -s "<statement>"
af release <node> --owner <id>

# Verifier workflow
af claim <node> --owner <id> --role verifier
af accept <node> --agent <id> [--confirm]
af challenge <node> --owner <id> --target <target> --severity <severity> --reason "<reason>"
af release <node> --owner <id>
```

---

## Context and References

- **Master document:** `./proof_master.md` (Version 2.0, corrected)
- **Next lemma handoff:** `./HANDOFF_LEMMA07.md`
- **Lemma 07 location:** `./lemmas/lemma07_commutator_g1g3/`
