# GNS Construction: Technical Learnings

This file indexes technical discoveries, gotchas, and insights gained during
implementation. **Errors are not failures** - they teach us what works and what doesn't.

Detailed learnings are organized by topic in the `learnings/` subdirectory.

---

## Index

### [State and Positivity](learnings/state-and-positivity.md)
- State Definition Requires Im = 0
- Conjugate Symmetry via Algebraic Polarization
- ℂ Has No Natural PartialOrder in Mathlib
- State Monotonicity via Spectral Ordering

### [Cauchy-Schwarz Proof](learnings/cauchy-schwarz-proof.md)
- Cauchy-Schwarz Proof Strategy (real vs complex parameters)
- Weak Cauchy-Schwarz Implementation
- Tight Cauchy-Schwarz: Optimal μ Selection
- Lean Implementation (avoiding simp, explicit rewrites)

### [Quotient Construction](learnings/quotient-construction.md)
- Quotient Module Construction in Mathlib (key APIs)
- Well-Definedness for Binary Functions on Quotients

### [Inner Product Conventions](learnings/inner-product-conventions.md)
- Inner Product Convention Mismatch (Physics vs Math)
- Building InnerProductSpace from Core (Instance Chain)
- State Spectral Ordering and Boundedness

### [Completion and Topology](learnings/completion-topology.md)
- Extending ContinuousLinearMap to Completion
- Typeclass Diamond in GNS Quotient Topology

### [Project Audit](learnings/project-audit.md)
- Documentation Drift Detection
- Left Ideal Property DOES Use Cauchy-Schwarz (Corrected)

---

## Quick Reference: Common Patterns

### Quotient Induction
```lean
obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
```

### Completion Induction
```lean
UniformSpace.Completion.induction_on₂ x y
  (fun hp => isClosed_eq <cont1> <cont2>)
  (fun a b => ...)
```

### Explicit Topology Selection
```lean
@ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ) φ.gnsQuotient
  (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace)
  ...
```

### Inner Product Convention Swap
```lean
instance gnsQuotientInner : Inner ℂ φ.gnsQuotient :=
  ⟨fun x y => φ.gnsInner y x⟩  -- Swap for math convention
```

---

## Template for New Entries

Add new learnings to the appropriate topic file in `learnings/`. Use this format:

```markdown
## Brief Title

**Discovery:** What you found

**Problem:** Why it matters

**Resolution:** How you fixed/addressed it

**Lesson:** General takeaway for future work
```
