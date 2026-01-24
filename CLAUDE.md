# AF-Tests: Lean 4 Formalization Project

## 🏆 GOLDEN RULES 🏆

> **ERRORS are NOT failures.** Document learnings and negative results instead.
> That is true success.

> **Incomplete work IS success.** STOP work before "simplifying" or "optimizing".

> **DOCUMENTATION is SUCCESS.** Write what you learned in `docs/*/LEARNINGS.md`.

---

## Current Projects

### GNS Construction (Active)
Formalizing the Gelfand-Naimark-Segal construction in Lean 4.

**Documentation:** `docs/GNS/README.md`
**Code:** `AfTests/GNS/`
**Learnings:** `docs/GNS/LEARNINGS.md`

See [docs/GNS/README.md](docs/GNS/README.md) for full plan and status.

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

### Document Everything
When you discover something interesting:
1. Add it to the relevant `docs/*/LEARNINGS.md`
2. This is SUCCESS even if the original task isn't complete

---

## Directory Structure

```
af-tests/
├── CLAUDE.md           # This file
├── HANDOFF.md          # Session handoff state
├── docs/
│   └── GNS/
│       ├── README.md       # GNS overview
│       ├── LEARNINGS.md    # Technical discoveries
│       └── phases/         # Detailed phase docs
└── AfTests/
    └── GNS/
        ├── State/          # Phase 1
        ├── NullSpace/      # Phase 2
        ├── PreHilbert/     # Phase 3
        ├── HilbertSpace/   # Phase 4
        ├── Representation/ # Phase 5
        └── Main/           # Phase 6
```

---

## Commands

```bash
# Build
lake build                              # Build all
lake build AfTests.GNS.State.Basic      # Build specific

# Check LOC
wc -l AfTests/**/*.lean | sort -n       # Lean files
wc -l docs/**/*.md | sort -n            # Doc files

# Find sorries
grep -rn "sorry" AfTests/ --include="*.lean"
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
Add any discoveries to `docs/*/LEARNINGS.md`

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
