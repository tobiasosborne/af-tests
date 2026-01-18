# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Project-Specific Issue Conventions

### Priority Levels
- **P0**: Blocking (build broken, >200 LOC violation)
- **P1**: High (sorry elimination, correctness bugs)
- **P2**: Medium (optimization, missing mathlib lemma)
- **P3**: Low (documentation, style)

### Creating Issues
```bash
bd new -p P0 -t "Title"      # Create issue
bd new -p P1 -t "Eliminate sorry: Lemma05.lean:42"
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

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds

