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

1. **Update HANDOFF.md** - Create/update `HANDOFF.md` in project root:
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
   ## Known Issues / Gotchas
   - [Any context the next agent needs]
   ## Files Modified
   - [List of files changed]
   ```
2. **File issues for remaining work** - Create issues for anything that needs follow-up
3. **Run quality gates** (if code changed) - `lake build`, check for errors
4. **Update issue status** - Close finished work, update in-progress items
5. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git add -A
   git commit -m "Session: <summary>"
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
6. **Verify checklist**:
   - [ ] HANDOFF.md updated
   - [ ] All changes committed and pushed
   - [ ] Beads synced
   - [ ] No uncommitted work left behind

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds
- ALWAYS update HANDOFF.md - next agent depends on it

