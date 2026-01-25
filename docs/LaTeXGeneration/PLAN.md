# LaTeX Generation Plan

## Goal
Generate a complete, human-readable LaTeX document from the Lean 4 source code.

## Constraints
- Each work unit ≤ 300 LOC output
- Use only the Lean source as input
- Parallelizable via subagents

---

## Document Structure

```
latex/
├── main.tex              # Master document
├── preamble.tex          # Packages, macros, theorem envs
├── chapters/
│   ├── 01-introduction.tex
│   ├── 02-algebra.tex
│   ├── 03-states.tex
│   ├── 04-boundedness.tex
│   ├── 05-topology.tex
│   ├── 06-seminorm.tex
│   ├── 07-dual.tex
│   ├── 08-gns.tex
│   ├── 09-representations.tex
│   └── 10-main-theorem.tex
└── appendix/
    └── lean-index.tex    # Index of all Lean declarations
```

---

## Work Units (Beads Issues)

### Phase 0: Setup (~150 LOC)
- **P0.1**: Create `main.tex` and `preamble.tex`

### Phase 1: Core Chapters (~1800 LOC total)

| ID | Chapter | Lean Files | Est. LaTeX LOC |
|----|---------|------------|----------------|
| P1.1 | Introduction | (none - overview) | ~100 |
| P1.2 | Algebra | FreeStarAlgebra, QuadraticModule, Archimedean | ~200 |
| P1.3 | States | MPositiveState, Props, NonEmptiness | ~250 |
| P1.4 | Boundedness | ArchimedeanBound, CauchySchwarzM, GeneratingCone | ~280 |
| P1.5 | Topology | StateTopology, SeminormTopology, Closedness, Compactness, Continuity | ~300 |
| P1.6 | Seminorm | StateSeminorm, SeminormProps, Closure | ~220 |
| P1.7a | Dual (Part 1) | Forward, SpanIntersection, SeparatingFunctional | ~280 |
| P1.7b | Dual (Part 2) | RieszApplication, ComplexExtension, Normalization | ~300 |

### Phase 2: GNS Chapter (~800 LOC, split into 3 parts)

| ID | Section | Lean Files | Est. LaTeX LOC |
|----|---------|------------|----------------|
| P2.1 | GNS Core | NullSpace, Quotient, PreRep | ~280 |
| P2.2 | GNS Completion | Bounded, Completion, Extension, Star | ~300 |
| P2.3 | GNS Complexification | Complexify, ComplexifyMap, ComplexifyInner, ComplexifyGNS, StarComplex, CompleteSpace, ExtensionComplex, CyclicIdentity, Constrained | ~300 |

### Phase 3: Final Chapters (~300 LOC)
| ID | Chapter | Lean Files | Est. LaTeX LOC |
|----|---------|------------|----------------|
| P3.1 | Representations | Constrained, VectorState, GNSConstrained | ~250 |
| P3.2 | Main Theorem | DualCharacterization, Theorem | ~150 |

### Phase 4: Appendix (~200 LOC)
- **P4.1**: Lean declaration index

---

## Template for Subagents

Each subagent receives this template and instructions:

```markdown
# Task: Convert [CHAPTER] to LaTeX

## Input Files
[List of .lean files to convert]

## Output File
latex/chapters/[XX-name].tex

## Template Structure
See TEMPLATE.md for the exact format to follow.

## Rules
1. Extract ALL definitions, theorems, lemmas from the Lean files
2. Convert Lean syntax to mathematical LaTeX
3. Include proof sketches (not full tactic proofs)
4. Preserve docstrings as prose explanations
5. Cross-reference other sections where appropriate
6. Output ≤ 300 LOC
```

---

## Conversion Rules

### Lean → LaTeX Mapping

| Lean | LaTeX |
|------|-------|
| `def foo : Type` | `\begin{definition}[foo]` |
| `theorem bar : P` | `\begin{theorem}[bar]` |
| `lemma baz : P` | `\begin{lemma}[baz]` |
| `structure S` | `\begin{definition}[S (Structure)]` |
| `class C` | `\begin{definition}[C (Class)]` |
| `instance` | (usually inline or omit) |
| `example` | `\begin{example}` |
| `/-! ... -/` | Section prose |
| `/-- ... -/` | Item description |

### Type Notation

| Lean | LaTeX |
|------|-------|
| `ℕ` | `\mathbb{N}` |
| `ℝ` | `\mathbb{R}` |
| `ℂ` | `\mathbb{C}` |
| `→` | `\to` |
| `∀` | `\forall` |
| `∃` | `\exists` |
| `∈` | `\in` |
| `≤` | `\le` |
| `star a` | `a^*` |
| `⟪x, y⟫` | `\langle x, y \rangle` |
| `‖x‖` | `\|x\|` |

---

## Dependencies

```
P0.1 (Setup)
  └─► P1.1, P1.2, P1.3, P1.4, P1.5, P1.6, P1.7a, P1.7b (parallel)
        └─► P2.1, P2.2, P2.3 (parallel, after P1.*)
              └─► P3.1, P3.2 (parallel, after P2.*)
                    └─► P4.1 (after all)
```

---

## Success Criteria

- [ ] All 44 Lean files represented
- [ ] All definitions/theorems included
- [ ] Compiles with pdflatex
- [ ] Human-readable mathematical prose
- [ ] ≤ 300 LOC per file
