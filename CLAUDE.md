# CLAUDE.md — AF-Tests Lean 4

Lean 4 formalization for operator algebras and Jordan algebras.

---

## GOLDEN RULES

> **OUTPUT = LEAN CODE.** Every issue = Lean file modified.
> **ERRORS ≠ FAILURES.** Document learnings. That is success.
> **INCOMPLETE = SUCCESS.** A sorry with notes > broken proof.
> **SMALL DELTAS.** Target ≤50 LOC. Max 200 LOC/file.
> **MATHLIB FIRST.** Search before implementing.

---

## The Simplification Trap

When context fills and proofs aren't working, you will feel the urge to "simplify" or "clean up" the code.

**THIS IS THE TRAP.**

This urge is your signal to STOP, not to delete.

| Correct | Wrong |
|---------|-------|
| Checkpoint, document, create issue | Delete "unnecessary" code |
| Commit what compiles | Rewrite approach |
| Update HANDOFF.md | "One more try" |
| Session complete | Simplify for "clarity" |

---

## NEVER (session failure)

- Delete working code to "simplify"
- Rewrite proof approach after 3 failed attempts
- Remove structure "for clarity"
- Add types/docstrings to unchanged code
- Refactor adjacent code
- Continue past checkpoint warnings

---

## Success Criteria

✓ sorry with documented goal state + approach
✓ Proof attempt that reveals why approach fails
✓ Discovery that lemma doesn't exist in mathlib
✓ 10 LOC that compiles
✓ Incomplete work with HANDOFF.md update

✗ 50 LOC that doesn't compile
✗ "Simplified" proof that deleted working parts
✗ Thrashing through multiple approaches

---

## Session Flow

### Start
1. Read HANDOFF.md
2. `bd ready` → select ONE issue (smallest P0/P1/P2)

### Execute
- Search mathlib: `lean_loogle`, `lean_leansearch`, `lean_local_search`
- Build often: `lake build`
- Stop at 3 failed attempts on same approach

### Checkpoint (at 35%+ context OR when stuck)
1. `lake build` — capture state
2. Commit: `git commit -m "WIP: [state]"`
3. Update HANDOFF.md
4. `bd create` for remaining work
5. `bd sync`
6. **Done. This is success.**

### Close
```
[ ] BUILD PASSES
[ ] HANDOFF.MD UPDATED
[ ] bd close → bd sync
[ ] git commit → git push
```

---

## GAPS = ISSUES

When you discover: "not in mathlib", "needs N LOC", "TODO", "sorry"

→ `bd create --title="..." --type=task --priority=2`

**Undocumented gaps = lost work.**

---

## Stop Signals

If you notice any of these, checkpoint immediately:
- Considering "simplifying" existing code
- Third attempt at same approach
- Tempted to delete and restart
- Thinking "if I just clean this up..."
- Same error message repeating
- Context checkpoint warning appeared

---

## References

- **Code:** `AfTests/Jordan/` (active), `AfTests/GNS/` (complete)
- **Books:** `examples3/Jordan Operator Algebras/`
- **Learnings:** `docs/*/LEARNINGS*.md`
