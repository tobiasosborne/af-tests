# Project Audit Learnings

Discoveries from systematic project audits and corrections.

---

## Project Audit - Documentation Drift Detection

**Discovery:** A systematic audit of the GNS subproject revealed 8 instances of
drift between documentation and implementation.

**Key Findings:**

1. **Naming mismatch** - `01_states.md` documents `State.cauchy_schwarz` but actual
   theorem is `State.inner_mul_le_norm_mul_norm`

2. **Misplaced theorem** - `null_space_left_ideal` is in CauchySchwarz.lean but:
   - Proof requires "boundedness", not Cauchy-Schwarz
   - Separate beads issue exists for NullSpace/LeftIdeal.lean
   - Creates unclear responsibility boundaries

3. **Status terminology** - "DONE" vs "Ready" undefined. Phase 1 marked "DONE"
   but has 4 sorries. Is "DONE" = structure complete, or fully proven?

4. **LOC target drift** - CauchySchwarz planned 50-70 LOC, actual 95 LOC

5. **Stale line numbers** - HANDOFF.md line numbers off by 1

**Resolution:** Created beads issues to track all findings with appropriate priorities.

**Lesson:** Regular audits catch drift before it compounds. Documentation that
isn't systematically verified against implementation will diverge. Consider
automated checks (e.g., grep for documented names in code).

---

## Left Ideal Property DOES Use Cauchy-Schwarz (Corrected)

**Discovery:** The left ideal property (ba ∈ N_φ when a ∈ N_φ) CAN be proven
using Cauchy-Schwarz, contrary to an earlier incorrect claim about boundedness.

**Proof (implemented in NullSpace/LeftIdeal.lean):**
1. Need: φ((ba)*(ba)) = 0 when φ(a*a) = 0
2. Compute: (ba)*(ba) = a* b* b a = a* · (b*ba)
3. By Cauchy-Schwarz (swapped): |φ(a* · x)|² ≤ φ(x*x).re · φ(a*a).re
4. Since φ(a*a) = 0, we get φ(a* · x) = 0 for all x
5. Taking x = b*ba gives φ((ba)*(ba)) = 0

**Key insight:** The "swapped" Cauchy-Schwarz lemma:
- Original: `apply_star_mul_eq_zero_of_apply_star_self_eq_zero` gives φ(x*a) = 0
- Swapped: `apply_mul_star_eq_zero_of_apply_star_self_eq_zero` gives φ(a*x) = 0
Both follow from the same `inner_mul_le_norm_mul_norm` theorem.

**Lesson:** When a proof seems to require a stronger hypothesis (like boundedness),
try rearranging the existing lemmas. The "swapped" version of a consequence may
be exactly what you need.
