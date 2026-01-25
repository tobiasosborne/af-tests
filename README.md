# AF-Tests: Formal Verification Projects in Lean 4

This repository contains two complete Lean 4 formalizations with accompanying documentation.

## Projects Overview

| Project | Description | Lean LOC | Sorries | Documentation |
|---------|-------------|----------|---------|---------------|
| [Archimedean Closure](#archimedean-closure) | Positivity in constrained *-representations | 4,943 | 0 | 75-page LaTeX |
| [Three-Cycle Groups](#three-cycle-permutation-groups) | Classification of permutation groups | 12,218 | 0 | LaTeX summary |

---

## Archimedean Closure

A complete formalization of the characterization of positivity in constrained *-algebra representations.

### Main Theorem

For the free *-algebra A₀ = ℂ⟨g₁,...,gₙ⟩ on n self-adjoint generators and quadratic module M:

> **A ∈ M̄ ⟺ π(A) ≥ 0 for all constrained *-representations π**

### Key Files

| Location | Description |
|----------|-------------|
| `AfTests/ArchimedeanClosure/` | Lean source (4,943 LOC) |
| `AfTests/GNS/` | GNS infrastructure (2,455 LOC) |
| `latex/main.pdf` | 75-page documentation |
| `docs/ArchimedeanClosure/` | Architecture and learnings |

### Proof Phases

1. **Algebra**: Free *-algebra, quadratic module, Archimedean property
2. **States**: M-positive states, S_M ≠ ∅
3. **Boundedness**: Cauchy-Schwarz, uniform bounds
4. **Topology**: Compactness via Tychonoff
5. **Seminorm**: ‖·‖_M definition and properties
6. **Dual**: Riesz extension → A ∈ M̄ ⟺ ∀φ, φ(A) ≥ 0
7. **Representations**: Constrained reps, vector states
8. **Main**: Combine with GNS construction

---

## Three-Cycle Permutation Groups

A complete formalization proving that certain three-generator permutation groups equal either A_N or S_N.

### Main Theorem

For generators g₁, g₂, g₃ as specific cycles on Ω = {0,...,5+n+k+m}:

> **H = ⟨g₁, g₂, g₃⟩ = A_N** if n, k, m all odd
>
> **H = ⟨g₁, g₂, g₃⟩ = S_N** if any of n, k, m is even

### Key Results (All Formally Verified)

| Lemma | Statement | LOC |
|-------|-----------|-----|
| Transitivity | H acts transitively on Ω | 585 |
| Base Case | Structure when n+k+m small | 740 |
| Primitivity | No non-trivial block systems | 5,192 |
| 3-Cycle Extraction | Commutators yield 3-cycles | 4,671 |
| Sign Analysis | Parity of generators | 611 |

### Key Files

| Location | Description |
|----------|-------------|
| `AfTests/ThreeCycle/` | Three-cycle proofs (4,671 LOC) |
| `AfTests/Primitivity/` | Primitivity proof (5,192 LOC) |
| `AfTests/Transitivity/` | Transitivity proof (585 LOC) |
| `AfTests/BaseCase/` | Base case analysis (740 LOC) |
| `AfTests/SignAnalysis/` | Parity analysis (611 LOC) |
| `AfTests/Core/` | Shared definitions (419 LOC) |
| `latex/three-cycle/theorem_statement.pdf` | Theorem statement |
| `examples/` | Proof development notes |

---

## Repository Structure

```
af-tests/
├── AfTests/                    # Lean 4 source code
│   ├── ArchimedeanClosure/     # Archimedean closure (4,943 LOC)
│   ├── GNS/                    # GNS infrastructure (2,455 LOC)
│   ├── ThreeCycle/             # 3-cycle extraction (4,671 LOC)
│   ├── Primitivity/            # Primitivity proof (5,192 LOC)
│   ├── Transitivity/           # Transitivity (585 LOC)
│   ├── BaseCase/               # Base cases (740 LOC)
│   ├── SignAnalysis/           # Sign/parity (611 LOC)
│   └── Core/                   # Core definitions (419 LOC)
│
├── latex/
│   ├── main.tex                # Archimedean closure document
│   ├── main.pdf                # Compiled (75 pages)
│   ├── chapters/               # 10 chapters
│   ├── appendix/               # Appendices
│   └── three-cycle/            # Permutation groups docs
│       └── theorem_statement.pdf
│
├── docs/                       # Project documentation
│   ├── ArchimedeanClosure/     # Architecture, learnings
│   ├── GNS/                    # GNS docs
│   └── LaTeXGeneration/        # LaTeX generation plan
│
├── examples/                   # Development notes
│   ├── lemmas/                 # Lemma-by-lemma proofs
│   └── proof_master.md         # Proof outline
│
├── CLAUDE.md                   # Development instructions
├── HANDOFF.md                  # Session state
└── AGENTS.md                   # Multi-agent coordination
```

## Building

### Lean
```bash
lake build
```

### LaTeX (Archimedean Closure)
```bash
cd latex
pdflatex main.tex && pdflatex main.tex
```

### LaTeX (Three-Cycle)
```bash
cd latex/three-cycle
pdflatex theorem_statement.tex
```

## Statistics

| Metric | Value |
|--------|-------|
| Total Lean files | 90+ |
| Total Lean LOC | ~20,000 |
| Sorries | **0** |
| LaTeX pages | 75+ |

## Axioms Used

Both projects use only standard Lean/Mathlib axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)
- `native_decide` support (for computational proofs)

## License

MIT License

## Acknowledgments

- Lean 4
- Mathlib4
- Claude Code for development assistance
