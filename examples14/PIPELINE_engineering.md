# The Feynman Integral Pipeline: A Software Engineering Audit

**Companion to SURVEY_feynman_integral_evaluation.md**
**Compiled: April 2026**

---

## Executive Summary

The multi-loop Feynman integral pipeline is a chain of ~6 specialized tools
connected by ad-hoc glue scripts with no standard interchange format. The
ecosystem comprises roughly **500k–700k LOC** across 15+ tools written in
Fortran, C++, Mathematica, FORM, Python, and Julia. There is massive functional
duplication — three independent C++ implementations of the Laporta algorithm,
three independent finite-field reconstruction libraries, two independent sector
decomposition codes — with essentially zero shared code between competing
tools. Testing is sparse to nonexistent in most tools. The pipeline is best
described as "artisanal" — a typical two-loop calculation represents 1–3 years
of work, with substantial manual intervention at each stage.

---

## 1. The Pipeline: What Happens When You Want All Diagrams to Order L

```
┌──────────────────────────────────────────────────────┐
│ Stage 1: DIAGRAM GENERATION                          │
│   QGRAF (Fortran) or FeynArts (Mathematica)          │
│   Input: model file + process spec + loop order       │
│   Output: symbolic list of diagrams (text)            │
└──────────────┬───────────────────────────────────────┘
               │  custom style file / glue scripts
               ▼
┌──────────────────────────────────────────────────────┐
│ Stage 2: ALGEBRAIC PROCESSING                        │
│   FORM (C, 171k LOC) or FeynCalc (Mathematica, 103k) │
│   Apply Feynman rules, Dirac traces, color algebra    │
│   Output: scalar integrals with numerators            │
└──────────────┬───────────────────────────────────────┘
               │  custom FORM/Python scripts
               ▼
┌──────────────────────────────────────────────────────┐
│ Stage 3: TOPOLOGY IDENTIFICATION                     │
│   Pak's algorithm via:                                │
│   - FeynCalc (FCLoopFindTopologyMappings)             │
│   - Tapir (Python)                                    │
│   - FIRE's tsort                                      │
│   Maps diagrams → minimal set of integral families    │
└──────────────┬───────────────────────────────────────┘
               │  topology definitions (YAML/text)
               ▼
┌──────────────────────────────────────────────────────┐
│ Stage 4: IBP REDUCTION  ★ THE BOTTLENECK ★           │
│   FIRE 7 (C++) or Kira 3 (C++) or LiteRed (Mma)      │
│   Optionally preceded by:                             │
│     NeatIBP (syzygy) or Blade (block-triangular)      │
│   Output: master integral decomposition               │
└──────────────┬───────────────────────────────────────┘
               │  reduction tables (rational functions)
               ▼
┌──────────────────────────────────────────────────────┐
│ Stage 5: MASTER INTEGRAL EVALUATION                  │
│   Analytical: differential equations (Henn canonical)  │
│   Numerical: AMFlow, DiffExp, pySecDec, FIESTA        │
│   Output: MI values as functions of kinematics        │
└──────────────┬───────────────────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────────────────┐
│ Stage 6: ASSEMBLY                                    │
│   (IBP coefficients) × (MI values) = amplitude        │
│   → cross sections, distributions, Monte Carlo        │
└──────────────────────────────────────────────────────┘
```

### Answer to "Do I use QGRAF or FeynCalc?"

**Both, for different things.** QGRAF generates diagrams; FeynCalc processes
them algebraically. They are not alternatives — they are sequential stages.
The choice is:

- **QGRAF → FORM**: The industrial-strength path. QGRAF is faster for large
  diagram counts and FORM handles expressions that would crash Mathematica.
  Used for all serious multi-loop calculations.

- **FeynArts → FeynCalc**: The Mathematica-native path. More user-friendly,
  visual diagrams, but slower. Practical for one-loop and simpler two-loop
  calculations. FeynCalc can also import QGRAF output via FeynHelpers.

### Answer to "Do they both use Pak's algorithm?"

**Neither QGRAF nor FeynArts uses Pak's algorithm.** Pak's algorithm for
topology identification is a downstream step, implemented in:

- **FeynCalc** (since v10): `FCLoopFindTopologyMappings` — the most accessible
  public implementation
- **Tapir** (Python): A dedicated topology identification tool
- **FIRE**: Has a `tsort` utility by Pak himself

QGRAF has its own graph-isomorphism detection to avoid generating duplicate
diagrams, but topology identification (grouping different diagrams into shared
integral families) is a separate, later step.

---

## 2. The Tools: Engineering Facts

### Codebase Size Comparison

| Tool | Language | Est. LOC | Test Suite | License | Active |
|------|----------|----------|------------|---------|--------|
| **FORM** | C/C++ | ~171k | 13 test files (~13k LOC), CI via GitHub Actions | GPL-3.0 | Yes (v5.0, Jan 2026) |
| **FeynCalc** | Mathematica | ~103k (core) | 300+ test files (~145k LOC tests) | GPL-3.0 | Yes (v10.2, Dec 2025) |
| **FIRE** | C++/Mathematica | ~680k (incl. test data) | `make test` available | GPLv2 | Yes (v7, Oct 2025) |
| **Kira** | C++ | ~50-100k (est.) | Benchmarks only | GPLv3 | Yes (v3, May 2025) |
| **pySecDec** | C++/Python | ~large (2334 commits) | Comprehensive (unittest + integration) | GPLv3 | Yes (v1.6.6, Oct 2025) |
| **FireFly** | C++ | moderate (1222 commits) | Yes (test/ dir, Travis CI) | GPLv3 | Yes (Sep 2025) |
| **FiniteFlow** | C++/Mathematica | moderate (73 commits) | Yes (tests/ dir) | MIT | Yes (Oct 2024) |
| **NeatIBP** | Mathematica/C | small (~33 files) | Examples only | GPLv3 | Yes (Jun 2025) |
| **Blade** | Mathematica | small-moderate | Paper benchmarks only | MIT | Yes (2024) |
| **AMFlow** | Mathematica | small (156 commits) | None documented | MIT | Yes (2022-23) |
| **LiteRed2** | Mathematica | small (single .m file) | None | Unspecified | Semi-active (2023) |
| **FeynArts** | Mathematica | ~34k (incl. models) | None documented | LGPL | Yes (v3.12, Mar 2025) |
| **FeynHelpers** | Mathematica | ~18k | None documented | GPL-3.0 | Yes (v2.0, Dec 2025) |
| **FormCalc** | Mathematica/FORM | ~50k (est.) | None documented | LGPL | Yes (v9.10, Oct 2024) |
| **QGRAF** | Fortran | ~5-10k | Example files only | Free academic (not OSS) | Yes (~v3.6, 2023-24) |
| **Reduze** | C++ | ~55k | Test data included | Unspecified | Dormant (~2015) |
| **FIESTA** | Mathematica/C++ | moderate | None documented | GPLv3 | Semi-active (2022) |

**Rough total across all tools: 500k–700k LOC**

### Testing Quality

The testing situation is **poor by modern software engineering standards**:

| Quality Level | Tools |
|---------------|-------|
| **Good** (CI, systematic tests) | FORM (GitHub Actions + Coveralls), pySecDec (unittest + integration), FireFly (Travis CI) |
| **Basic** (some tests) | FIRE (`make test`), FiniteFlow (test dir), FeynCalc (300+ MUnit tests, but no CI) |
| **Examples only** | NeatIBP, Blade, QGRAF |
| **None documented** | Kira, AMFlow, LiteRed, FeynArts, FormCalc, FIESTA, FeynHelpers |

The most widely-used tool (Kira) has no documented test suite. Validation
in HEP relies primarily on **cross-checking between independent tools** (run
the same calculation in FIRE and Kira, compare results) rather than unit
testing.

---

## 3. The Duplication Problem

### Laporta Algorithm: 3 Independent Implementations

FIRE, Kira, and Reduze all independently implement the same Laporta algorithm
in C++ from scratch. They share **zero code**.

| Aspect | FIRE 7 | Kira 3 | Reduze 2 |
|--------|--------|--------|----------|
| Symbolic engine | FLINT/Fermat/Symbolica | GiNaC + Fermat | GiNaC |
| Database backend | KyotoCabinet | In-memory | Custom |
| Finite field | Built-in | FireFly (linked library) | No |
| Parallelism | MPI | Threads + FireFly | Distributed jobs |
| Status | Very active | Very active | Dormant |

Each is likely 50,000–100,000+ lines of non-trivial C++. This is the largest
area of duplication.

### Finite-Field Reconstruction: 3 Independent Implementations

| Implementation | Used by | LOC (est.) |
|----------------|---------|------------|
| FireFly | Kira | Moderate (1222 commits) |
| FiniteFlow | Blade | Moderate (73 commits) |
| FIRE built-in | FIRE 7 | Part of FIRE codebase |

All three implement essentially the same mathematical algorithms (Ben-Or/Tiwari,
Zippel, Chinese Remainder Theorem) independently.

### Sector Decomposition: 2 Independent Implementations

| Tool | Language | Key Feature |
|------|----------|-------------|
| pySecDec | Python/C++ | PyPI distribution, ReadTheDocs, comprehensive tests |
| FIESTA | Mathematica/C++ | GPU support, Tensor Train integrator |

Both use the Cuba library for Monte Carlo integration. Both share the same
mathematical foundation but no code.

### IBP System Generation: 2 Approaches

| Tool | Method | Output feeds into |
|------|--------|-------------------|
| NeatIBP | Syzygy/module intersection | Kira |
| Blade | Block-triangular decomposition | FiniteFlow |

These are genuinely different algorithms solving the same optimization problem.

### Summary

| Function | Independent implementations | Shared code? |
|----------|---------------------------|--------------|
| Laporta algorithm | 3 (FIRE, Kira, Reduze) | None |
| Finite-field reconstruction | 3 (FireFly, FiniteFlow, FIRE) | None |
| Sector decomposition | 2 (pySecDec, FIESTA) | None |
| IBP system generation | 2 (NeatIBP, Blade) | None |
| Topology identification | 3 (FeynCalc, Tapir, FIRE/tsort) | None |
| Diagram generation | 2 (QGRAF, FeynArts) | None |

**This is the classic academic software pattern**: each group builds their own
complete implementation. There is essentially no shared code between competing
tools. The interoperation that exists is at the interface level (file formats,
configuration) rather than shared libraries.

---

## 4. Interchange Formats: The Ugly Reality

**There is no universal standard interchange format.** Each tool has its own:

| Tool | Input Format | Output Format |
|------|-------------|---------------|
| QGRAF | Model file + style file | User-defined text (via style) |
| FORM | `.frm` files (own syntax) | `.frm` files |
| FeynCalc | Mathematica expressions (FAD, SPD, etc.) | Mathematica expressions |
| Kira | YAML topology definitions + text integral lists | Text reduction tables |
| FIRE | Mathematica-formatted input | Mathematica tables |
| NeatIBP | Mathematica input | Kira-compatible output (v1.1) |
| pySecDec | Python API | C++ code generation + numerical results |

**In practice**: Every group writes custom glue scripts — FORM programs, Python
parsers, Mathematica notebooks — that convert output from one tool into input
for the next. These scripts are rarely published, often brittle, tailored to
specific processes, and a major source of bugs.

Some standardization efforts:
- **FeynHelpers** provides export functions from FeynCalc to FIRE/Kira/QGRAF/pySecDec
- **NeatIBP 1.1** has an explicit Kira interface
- **LiteRed ships with FIRE 7** and generates rules FIRE consumes
- The concept of an "integral family specification" is shared, but syntax differs

---

## 5. Manual Intervention at Each Stage

| Stage | Automation | What a Human Does |
|-------|-----------|-------------------|
| Diagram generation | High | Write model + style files (reusable) |
| Algebraic processing | Medium | Write custom FORM code for the process |
| Topology identification | Medium-High | Setup, validate mappings |
| IBP reduction | High (once configured) | Topology definitions, resource management, babysit cluster jobs |
| Master integrals | Low-Medium | Often case-by-case analysis, dedicated research |
| Assembly | Low-Medium | Coefficient simplification, numerical stability |

**A typical two-loop calculation paper = 1–3 years of work by a small team.**

For well-studied process types (e.g., massless 2→2 at two loops), groups have
private automated pipelines. For new processes, significant manual setup is
required at each stage.

---

## 6. Pain Points

1. **IBP reduction is the bottleneck**: Linear systems with millions of equations.
   Two-loop 4-point with masses takes days/weeks on clusters. Three loops is heroic.

2. **No standard interchange format**: Custom glue code everywhere. Every group
   reinvents this wheel. Format conversion is a major source of bugs.

3. **Enormous intermediate expressions**: IBP coefficients can be megabytes of
   rational functions. Finite-field methods help but add pipeline complexity.

4. **Reproducibility crisis**: Many calculations depend on unpublished private
   code — "one physicist's collection of scripts that only they understand."

5. **Validation = running everything twice**: The main validation strategy is
   cross-checking between independent tools (FIRE vs Kira), which doubles work.

6. **Master integrals beyond polylogarithms**: When elliptic integrals appear
   (common with internal masses), the canonical form technology breaks down.

7. **Numerical instability**: Large cancellations in physical phase-space regions.

---

## 7. What a Real Calculation Looks Like

### Example: Two-loop QCD corrections to pp → tt̄

1. **QGRAF**: Generate O(500) diagrams
2. **FORM**: Custom code for projecting onto form factors, Dirac traces, color
3. **Topology ID**: Map to O(50-100) integral families
4. **IBP**: Kira + FIRE cross-checked, finite-field methods, days on clusters
5. **Master integrals**: Combination of DEs (massless) + dedicated numerical work (massive). Some MIs required separate multi-year efforts.
6. **Result**: 1–3 year project for a small team

### Example: Higgs at N3LO (3 loops)

- ~10,000 diagrams
- Hundreds of integral families
- IBP systems with millions of equations
- HPLs up to weight 6
- Months of cluster computation

---

## 8. Emerging Automation Efforts

| Framework | What it automates | Status |
|-----------|------------------|--------|
| **FeynCalc 10.2 + FeynHelpers 2.0** | Algebra → topology ID → IBP dispatch → evaluation | Most complete public pipeline |
| **LoopIn** (2026) | Full pipeline: generation → reduction → evaluation | Very recent, interface to multiple tools |
| **Caravel** | Unitarity-based multi-loop amplitudes over finite fields | Specialized, not public |
| **FormCalc** | FeynArts → FORM algebra → LoopTools evaluation | One-loop mature, two-loop limited |

The trend is clear: finite-field methods (avoid symbolic blowup) + AMFlow
(black-box numerical MI evaluation) + NeatIBP/Blade (smaller IBP systems)
are converging toward more automation. But as of 2026, cutting-edge multi-loop
calculations remain artisanal craftsmanship.

---

## 9. Dependency Graph

```
                    QGRAF (Fortran, closed-source)
                       │
              ┌────────┴────────┐
              │                 │
           FORM (C)        FeynCalc (Mma)
           171k LOC         103k LOC
              │                 │
              │            FeynHelpers (Mma, glue layer)
              │                 │
              ▼                 ▼
         ┌─────────────────────────┐
         │   Topology ID           │
         │   Pak's alg (FeynCalc)  │
         │   Tapir (Python)        │
         │   tsort (FIRE)          │
         └────────┬────────────────┘
                  │
    ┌─────────────┼──────────────┐
    │             │              │
    ▼             ▼              ▼
 NeatIBP       Blade        (direct)
 (syzygy)   (block-tri)
    │             │              │
    ▼             ▼              │
  Kira ◄──── FiniteFlow         │
  (C++)       (C++)             │
    │                           │
    │         ┌─────────────────┘
    ▼         ▼
  FIRE 7 ◄── LiteRed (bundled)
  (C++)      (Mma)
    │
    ├──── FireFly (C++, reconstruction)
    │
    ▼
 ┌─────────────────────────┐
 │   Master Integrals       │
 │   AMFlow (Mma)           │ ← calls FIRE/Kira for DE setup
 │   DiffExp (Mma)          │
 │   pySecDec (Py/C++)      │
 │   FIESTA (Mma/C++)       │
 └─────────────────────────┘
```

### Shared Dependencies

| Library | Used by |
|---------|---------|
| GiNaC/CLN | Kira, Reduze |
| GMP | FIRE, FiniteFlow, FireFly |
| FLINT | FIRE 7, FiniteFlow |
| Fermat (CAS) | FIRE, Kira, LiteRed |
| Cuba (Monte Carlo) | pySecDec, FIESTA |
| KyotoCabinet | FIRE, FIESTA |

---

*Based on research by 4 parallel investigation agents examining repositories,
documentation, and publications for 17 tools in the Feynman integral pipeline.*
