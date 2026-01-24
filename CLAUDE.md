# AF-Tests: Lean 4 Formalization Project

## GOLDEN RULES

> **ERRORS are NOT failures.** Document learnings and negative results instead.
> That is true success.

> **Incomplete work IS success.** STOP work before "simplifying" or "optimizing".

> **DOCUMENTATION is SUCCESS.** Write what you learned in `docs/*/LEARNINGS.md`.

---

## Current Projects

### Archimedean Closure (Active)
Formalizing the characterization of positivity in constrained C*-algebra representations.

**Main Theorem:** A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations

**Documentation:** `docs/ArchimedeanClosure/README.md`
**Architecture:** `docs/ArchimedeanClosure/ARCHITECTURE.md`
**File Plan:** `docs/ArchimedeanClosure/FILE_PLAN.md`
**Code:** `AfTests/ArchimedeanClosure/`

#### Key Concepts
1. **Free *-algebra A₀** = ℂ⟨g₁,...,gₙ⟩ with self-adjoint generators
2. **Quadratic module** M = {Σ aᵢ*aᵢ + Σ bⱼₖ*gⱼbⱼₖ}
3. **Archimedean property**: ∀a, ∃N, N·1 - a*a ∈ M
4. **M-positive state**: φ : A₀ → ℂ with φ(1)=1 and φ(m)≥0 for m∈M
5. **State seminorm**: ||a||_M = sup{|φ(a)| : φ ∈ S_M}

#### Implementation Phases
| Phase | Description | Est. LOC |
|-------|-------------|----------|
| 1 | Algebraic Setup (FreeStarAlgebra, QuadraticModule, Archimedean) | 140 |
| 2 | States (MPositiveState, NonEmptiness) | 120 |
| 3 | Boundedness (Cauchy-Schwarz, ArchimedeanBound, GeneratingCone) | 110 |
| 4 | Topology (StateTopology, Compactness) | 110 |
| 5 | Seminorm (StateSeminorm, Closure) | 105 |
| 6 | Dual Characterization (Riesz extension application) | 215 |
| 7 | Representations (Constrained, GNSConstrained) | 110 |
| 8 | Main Theorem | 55 |
| **Total** | | **~965** |

---

### GNS Construction (Complete)
Formalization of the Gelfand-Naimark-Segal construction. **FULLY PROVEN.**

**Documentation:** `docs/GNS/README.md`
**Learnings:** `docs/GNS/LEARNINGS.md`
**Code:** `AfTests/GNS/` (2,455 LOC, 0 sorries)

**Proven Theorems:**
- `State.gns_theorem` - GNS existence
- `State.gns_uniqueness` - Uniqueness up to unitary equivalence

**Reusable Infrastructure:**
- Cauchy-Schwarz for states (`AfTests/GNS/State/CauchySchwarz.lean`)
- State definition pattern
- Completion/density proof techniques

---

## Critical Rules

### 200 LOC Limit (ALL FILES)
**Every file MUST be ≤ 200 lines.** This includes:
- `.lean` files
- `.md` documentation files
- Any other source files

If a file exceeds 200 LOC:
```bash
bd create --title="Refactor: <File> exceeds 200 LOC" --type=task --priority=0
```

### Mathlib First
Always search mathlib before writing custom proofs:
- `lean_loogle` - type pattern search
- `lean_leansearch` - natural language search
- `lean_local_search` - verify lemma exists

### Key Mathlib for Archimedean Closure
```lean
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.Convex.Cone.Extension  -- Riesz extension!
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Compactness.Compact    -- Tychonoff
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Geometry.Convex.Cone.Basic
```

### Document Everything
When you discover something interesting:
1. Add it to the relevant `docs/*/LEARNINGS.md`
2. This is SUCCESS even if the original task isn't complete

### Status Terminology
Use these consistently in docs and HANDOFF:

| Status | Meaning | Sorries OK? |
|--------|---------|-------------|
| **Not Started** | No code written | N/A |
| **Ready** | Dependencies met, can begin work | N/A |
| **In Progress** | Currently being worked on | Yes |
| **Structure Done** | Definitions + statements complete | Yes |
| **Proven** | All sorries eliminated | No |

---

## Directory Structure

```
af-tests/
├── CLAUDE.md           # This file
├── HANDOFF.md          # Session handoff state
├── docs/
│   ├── ArchimedeanClosure/
│   │   ├── README.md       # Project overview
│   │   ├── ARCHITECTURE.md # High-level design
│   │   ├── FILE_PLAN.md    # Detailed file specs
│   │   └── LEARNINGS.md    # Technical discoveries
│   └── GNS/
│       ├── README.md       # GNS overview (complete)
│       └── LEARNINGS.md    # Technical discoveries
└── AfTests/
    ├── ArchimedeanClosure/
    │   ├── Algebra/        # Phase 1: FreeStarAlgebra, QuadraticModule
    │   ├── State/          # Phase 2: MPositiveState
    │   ├── Boundedness/    # Phase 3: Cauchy-Schwarz, bounds
    │   ├── Topology/       # Phase 4: Compactness
    │   ├── Seminorm/       # Phase 5: ||·||_M
    │   ├── Dual/           # Phase 6: Riesz extension
    │   ├── Representation/ # Phase 7: Constrained reps
    │   └── Main/           # Phase 8: Main theorem
    └── GNS/                # Complete GNS infrastructure
```

---

## Commands

```bash
# Build
lake build                                      # Build all
lake build AfTests.ArchimedeanClosure.Algebra.FreeStarAlgebra  # Build specific

# Check LOC
wc -l AfTests/**/*.lean | sort -n              # Lean files
wc -l docs/**/*.md | sort -n                   # Doc files

# Find sorries
grep -rn "sorry" AfTests/ArchimedeanClosure --include="*.lean"

# Verify GNS (should show 0 sorries)
grep -rn "sorry" AfTests/GNS --include="*.lean"
```

---

## Beads Issue Tracking

### Priority Levels
- **P0**: Blocking (build broken, >200 LOC violation)
- **P1**: High (sorry elimination, correctness bugs)
- **P2**: Medium (optimization, missing mathlib lemma)
- **P3**: Low (documentation, style)

### Commands
```bash
bd ready                  # What can I work on?
bd create --title="..." --type=task --priority=2
bd update <id> --status=in_progress
bd close <id>
bd sync
```

---

## Debugging

```bash
# Lean LSP tools
lean_goal           # See proof state
lean_diagnostic_messages   # See errors
lean_hover_info     # Get type info
lean_completions    # Autocomplete
```

---

## Landing the Plane (Session End)

**MANDATORY** checklist:

### 1. Document Learnings
Add any discoveries to `docs/ArchimedeanClosure/LEARNINGS.md`

### 2. Update HANDOFF.md
```markdown
# Handoff: [Date]
## Completed This Session
## Current State
## Next Steps
## Known Issues / Gotchas
## Files Modified
```

### 3. Update Issues
```bash
bd close <completed-ids>
bd sync
```

### 4. Commit and Push
```bash
git add -A
git commit -m "Session: <summary>"
bd sync
git push
git status  # MUST show "up to date with origin"
```

### 5. Verify
- [ ] Learnings documented
- [ ] HANDOFF.md updated
- [ ] All changes committed and pushed
- [ ] Beads synced

---

## Red Flags You're Deviating

- You're introducing hypotheses not in the plan
- You're using a different case structure than the plan
- You're "simplifying" or "optimizing" the proof approach
- You can't point to the exact step in the plan your code implements

**STOP and re-read the plan if any of these apply.**

---

## Risk Assessment (Archimedean Closure)

### Low Risk (mathlib support strong)
- Tychonoff theorem
- Riesz extension
- Cone closures
- Seminorm properties

### Medium Risk (need custom work)
- Free *-algebra with SA generators
- M-positive state structure
- Seminorm ||·||_M definition

### High Risk (complex proofs)
- Quadratic module generating property
- GNS representation is constrained
- Seminorm equivalence proof
