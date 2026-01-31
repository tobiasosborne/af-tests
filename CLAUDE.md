# CLAUDE.md — AF-Tests Lean 4 Formalization

## Project Overview

Lean 4 formalization for operator algebras and Jordan algebras.

```
af-tests/
├── AfTests/
│   ├── GNS/                  # COMPLETE (0 sorries)
│   ├── ArchimedeanClosure/   # Structure done (0 sorries)
│   └── Jordan/               # Active (~21 sorries)
├── docs/*/LEARNINGS*.md      # Technical discoveries
└── examples3/                # Reference books
```

---

## GOLDEN RULES

> **OUTPUT IS LEAN CODE.** Every issue = Lean file created/modified.
> **ERRORS are NOT failures.** Document learnings. That is success.
> **Incomplete work IS success.** STOP before "simplifying."
> **Small deltas.** Target ≤50 LOC per session.
> **Mathlib first.** Always search before implementing.

---

## Session Protocol

### Phase 1: Orient
1. Read HANDOFF.md
2. `bd ready` — check issues
3. Select ONE issue (smallest unblocked P0/P1/P2)

### Phase 2: Execute
- Target ≤50 LOC, max 200 LOC/file
- Search mathlib first: `lean_loogle`, `lean_leansearch`
- Build: `lake build` — **MUST COMPILE**
- Update learnings

### Phase 3: Outcome
**Success:** Update HANDOFF, close issue, → Phase 4
**Problem:** Document attempt in learnings, create follow-up issues, → Phase 4

### Phase 4: Land the Plane
```
[ ] BUILD PASSING
[ ] LEARNINGS UPDATED
[ ] HANDOFF.MD UPDATED
[ ] ISSUES CLOSED — bd close, bd sync
[ ] COMMITTED AND PUSHED
```

---

## 🚨 GAPS = ISSUES 🚨

Trigger words requiring `bd create`:
- "not in mathlib", "needs implementation", "TODO", "sorry", "~N LOC"

**Documentation without issues = LOST WORK.**

---

## Current Projects

### Jordan Algebras (Active)
**Code:** `AfTests/Jordan/` | **Sorries:** ~21
**Reference:** Hanche-Olsen & Størmer (1984) → `examples3/Jordan Operator Algebras/`

Key sorries:
- `FormallyReal/Def.lean` — `of_sq_eq_zero`
- `FormallyReal/Spectrum.lean` — spectral theory
- `OperatorIdentities.lean` — idempotent identities

### GNS Construction (Complete)
`AfTests/GNS/` — 2,455 LOC, 0 sorries
Theorems: `State.gns_theorem`, `State.gns_uniqueness`

### Archimedean Closure (Structure Done)
`AfTests/ArchimedeanClosure/` — 0 sorries

---

## Mathlib First

```bash
lean_loogle "Type pattern"      # Type signature
lean_leansearch "description"   # Natural language
lean_local_search "name"        # Verify exists
```

Key imports:
```lean
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Cone.Extension
```

---

## Commands

```bash
lake build                      # Build all
grep -rn "sorry" AfTests/Jordan --include="*.lean"  # Find sorries

bd ready              # Available work
bd close <id>         # Close issue
bd sync               # Sync with git
```

---

## Issue Tracking

| Priority | Meaning |
|----------|---------|
| P0 | Blocking (build broken) |
| P1 | High (sorry elimination) |
| P2 | Medium (improvements) |
| P3 | Low (docs, style) |

---

## Deviation Detection

Red flags → STOP and document:
- Solving problem not in selected issue
- Changing unmentioned files
- Delta approaching 50 LOC, not done
- "Refactoring" unrelated code

---

## Handoff Template

```markdown
# Handoff: [Date] (Session N)

## Completed This Session
- <issue-id>: <summary>

## Current State
## Next Steps
## Known Issues
## Files Modified
```
