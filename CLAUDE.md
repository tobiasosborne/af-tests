# AF-Tests: Lean 4 Formalization Project

## Project Goal
Prove H = ⟨g₁,g₂,g₃⟩ equals Aₙ (if n,k,m all odd) or Sₙ (otherwise) for Ω = Fin(6+n+k+m).

## Critical Rules

### 200 LOC Limit
**Every `.lean` file MUST be ≤ 200 lines.** If you notice a file exceeds this:
```bash
bd new -p P0 -t "Refactor: <File>.lean exceeds 200 LOC"
```

### Mathlib First
Always search mathlib before writing custom proofs:
- `lean_loogle` - type pattern search
- `lean_leansearch` - natural language search
- `lean_local_search` - verify lemma exists

### Phases
- **Phase 1-2**: Sorries/axioms OK (scaffolding)
- **Phase 3**: Eliminate all sorries (Jordan axiom may remain)

## Directory Structure
```
AfTests/
├── Core/           # Omega, Generators, GroupH, Blocks
├── BaseCase/       # Lemmas 1-4
├── Transitivity/   # Lemma 5
├── ThreeCycle/     # Lemmas 6-9
├── Primitivity/    # Lemmas 10-11
├── SignAnalysis/   # Lemmas 12-15
└── MainTheorem.lean
```

## Index Convention
AF uses 1-indexed. Lean uses 0-indexed.
- AF element k → Lean `Fin.mk (k-1)`
- AF cycle (1 6 4) → Lean `c[0, 5, 3]`

## Key Mathlib Imports
```lean
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.Primitive
```

## Proof Strategies by Lemma Type

**Computational** (Lemmas 1, 4, 6-9): Use `native_decide`
```lean
theorem foo : bar := by native_decide
```

**Sign/Parity** (Lemmas 13-14): Use mathlib's `Equiv.Perm.sign_cycle`

**Structural** (Lemmas 2-3, 5, 10-11): Build explicit constructions

**Jordan** (Lemma 12): Axiom if not in mathlib

## Commands

```bash
lake build                              # Build all
lake build AfTests.BaseCase.Lemma01    # Build specific
grep -rn "sorry" AfTests/ --include="*.lean"  # Find sorries
wc -l AfTests/**/*.lean | sort -n      # Check LOC
```

## Beads Issue Tracking

### Priority Levels
- **P0**: Blocking (build broken, >200 LOC violation)
- **P1**: High (sorry elimination, correctness bugs)
- **P2**: Medium (optimization, missing mathlib lemma)
- **P3**: Low (documentation, style)

### Commands
```bash
bd new -p P0 -t "Title"      # Create issue
bd new -p P1 -t "Eliminate sorry: Lemma05.lean:42"
bd list                       # View all issues
bd list -p P0                 # View blocking issues only
bd show <id>                  # View issue details
bd close <id>                 # Close issue
bd comment <id> "note"        # Add comment
```

### When to Create Issues
| Trigger | Priority | Title Format |
|---------|----------|--------------|
| File > 200 LOC | P0 | `Refactor: <File>.lean exceeds 200 LOC` |
| Build broken | P0 | `Build: <error summary>` |
| Sorry to eliminate | P1 | `Eliminate sorry: <Lemma> line <N>` |
| Proof blocked | P1 | `Blocked: <Lemma> - <reason>` |
| Need mathlib lemma | P2 | `Mathlib: need <description>` |
| Cleanup/refactor | P3 | `Cleanup: <description>` |

## Reference Documents
- `examples/proof_master.md` - Canonical proof (v2.0 corrected)
- `examples/lemmas/main_theorem/HANDOFF_CONSOLIDATION_AND_LEANIFICATION.md` - Full context
- `examples/lemmas/lemma06_commutator_g1g2/ThreeCycleExtraction.lean` - Working example

## Quick Wins (Start Here)
1. Lemma 13 - cycle sign (mathlib direct)
2. Lemma 4 - cardinality (native_decide)
3. Lemma 14 - generator parity (uses Lemma 13)
4. Lemmas 6-8 - commutators (native_decide)

## Common Patterns

### Defining cycles on Fin n
```lean
def myCycle : Perm (Fin 7) := c[0, 6, 4] * c[1, 3, 5]
```

### Computational verification
```lean
theorem foo : myCycle 0 = 6 := by native_decide
```

### Group closure
```lean
def H : Subgroup (Perm (Fin n)) := Subgroup.closure {g₁, g₂, g₃}
```

## Debugging
- `lean_goal` - see proof state
- `lean_diagnostic_messages` - see errors
- `lean_hover_info` - get type info
- `lean_completions` - autocomplete

## Landing the Plane (Session End)

**MANDATORY** when ending a work session:

### 1. Update HANDOFF.md
Create/update `HANDOFF.md` in project root with:
```markdown
# Handoff: [Date]

## Completed This Session
- [List of completed tasks/issues]

## Current State
- Build status: [passing/failing]
- Sorry count: [N]
- Open blockers: [list or "none"]

## Next Steps (Priority Order)
1. [Most important next task]
2. [Second priority]
3. [Third priority]

## Known Issues / Gotchas
- [Any traps or context the next agent needs]

## Files Modified
- [List of files changed this session]
```

### 2. Update Issues
```bash
bd close <completed-ids>           # Close finished work
bd new -p P1 "Blocked: ..." -d "..." # File blockers
bd list -p P0                       # Verify no P0 open
```

### 3. Commit and Push
```bash
git add -A
git commit -m "Session: <summary>"
bd sync
git push
git status  # MUST show "up to date with origin"
```

### 4. Verify
- [ ] HANDOFF.md updated
- [ ] All changes committed and pushed
- [ ] Beads synced
- [ ] No uncommitted work left behind
