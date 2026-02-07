# CLAUDE.md — AF-Tests Lean 4

Lean 4 formalization for operator algebras and Jordan algebras.

---

## 🚨 HANCHE-OLSEN IS GROUND TRUTH — READ BEFORE THINKING 🚨

**Book location:** `examples3/Jordan Operator Algebras/joa-m/joa-m.md` (4688 lines)

**MANDATORY for ANY Macdonald/FundamentalFormula work:**
1. **Read the relevant H-O section FIRST** — before reasoning, before planning
2. **Cite line numbers** from joa-m.md in your proofs and memory files
3. **If you cannot cite a line number, you are hallucinating** — stop and read
4. **NEVER reason from first principles** about proof strategy when the book has the proof
5. **NEVER delete or "simplify" this section** — it has been removed ~30 times by agents

**Key H-O sections for current work:**
- Macdonald's theorem statement: 2.4.13 (search "2.4.13")
- M_{p,q} construction + properties (i)-(iv): 2.4.24 (line ~1215)
- Equation (2.58) — T_{x^k} M_{p,q}: lines 1326-1377
- Proof of Macdonald 2.4.25: lines 1379-1389
- Fundamental formula 2.4.18: search "2.4.18"

**The hallucination pattern:** Agents fill context with first-principles reasoning
("let me think about how to prove this...") and never read the book. The book
has the complete proof. Read it. Follow it. Cite it.

---

## BUILD COMMAND — READ THIS FIRST

**NEVER run `lake build` bare. It will rebuild all of mathlib from scratch (~2 hours).**

The correct build command is:
```bash
lake build AfTests 2>&1 | tail -40
```

This builds ONLY the project modules, using the pre-built mathlib cache. If you see
mathlib files compiling, STOP IMMEDIATELY (Ctrl+C) — something is wrong.

For checking a single file:
```bash
lake env lean AfTests/Jordan/SomeFile.lean 2>&1
```

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
- Build often: `lake build AfTests` (NEVER bare `lake build`!)
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

- **H-O BOOK (GROUND TRUTH):** `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- **Code:** `AfTests/Jordan/` (active), `AfTests/GNS/` (complete)
- **Learnings:** `docs/*/LEARNINGS*.md`, `memory/*.md`
- **NEVER remove the H-O section at the top of this file**
