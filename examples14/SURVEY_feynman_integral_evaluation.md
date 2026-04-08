# The State of Automated Feynman Integral Evaluation (2026)

**A survey prompted by arXiv:2604.05025 (Huang, Ma, Wang & Yang)**
**Compiled: April 2026**

---

## Executive Summary

Feynman integral evaluation is the computational backbone of precision perturbative QFT. The field has matured from manual calculations to a sophisticated automated pipeline, but is hitting computational walls at the multi-loop multi-leg frontier demanded by the HL-LHC program. Three major paradigms compete and complement each other:

1. **Integration-by-parts (IBP) reduction** — the 40-year workhorse, now powered by finite-field arithmetic and syzygy methods
2. **Intersection theory** — a mathematically elegant alternative using twisted cohomology, rapidly maturing since 2018
3. **The branch representation** (2024-2026) — a new Feynman-parametric reformulation that dramatically reduces the variable count in intersection-theory computations

The paper arXiv:2604.05025 sits at the confluence of (2) and (3), achieving a factor-of-38 speedup on test cases and reducing the intersection-theory variable count to at most 3L-3 for L-loop integrals regardless of leg count.

---

## 1. The Standard Pipeline

The modern end-to-end workflow for evaluating multi-loop Feynman integrals proceeds through five stages:

### Stage 1: Diagram Generation & Topology Identification
- **QGRAF**: High-performance diagram generator
- **FeynArts / FeynCalc 10.2**: Diagram generation, algebraic manipulation
- Topologies are identified and minimized using Pak's canonical form algorithms

### Stage 2: IBP Reduction to Master Integrals
Express all integrals in a family as linear combinations of a minimal set of "master integrals" (MIs). This is the dominant computational bottleneck.

### Stage 3: Differential Equations
Master integrals satisfy systems of first-order linear ODEs in kinematic invariants. Finding a **canonical (epsilon) form** (Henn 2013) makes the solution trivial order-by-order in the dimensional regulator.

### Stage 4: Boundary Conditions
Determined from regularity conditions at special kinematic points (soft/collinear limits, thresholds).

### Stage 5: Numerical Evaluation
Series expansion (AMFlow, DiffExp), sector decomposition (pySecDec, FIESTA5), or direct analytic evaluation in terms of multiple polylogarithms.

---

## 2. IBP Reduction: The Workhorse

### Foundations
- **Tkachov (1981)**: Discovered that integrals of total derivatives vanish in dimensional regularization, producing linear relations among Feynman integrals with shifted propagator powers.
- **Chetyrkin & Tkachov (1981)**: Developed IBP into a systematic algorithm, proving all 4-loop counterterms are algorithmically calculable.
- **Laporta (2001)**: Systematized practical IBP into the "Laporta algorithm" — generate a large overdetermined system by substituting many seed values, then solve by Gaussian elimination. Every modern IBP tool implements some variant.

### The Finite-Field Revolution
The critical modern innovation: instead of manipulating enormous rational functions symbolically (intermediate expressions can reach gigabytes), perform the entire reduction numerically modulo large primes, then reconstruct exact rational coefficients via the Chinese Remainder Theorem. Pioneered by **von Manteuffel & Schabinger (2016)**.

### Current Software Landscape

| Tool | Language | License | Latest Version | Status | Key Advantage |
|------|----------|---------|---------------|--------|---------------|
| **FIRE** | C++/Mathematica | GPLv2 | 7 (Oct 2025) | Active | Fully automated modular pipeline, MPI parallel |
| **Kira** | C++ | GPLv3 | 3 (May 2025) | Active | Optimized seeding, integrated FireFly reconstruction |
| **NeatIBP** | Mathematica/C | GPL-3.0 | 1.1 (Jun 2025) | Active | Syzygy-based: generates much smaller IBP systems |
| **Blade** | Mathematica | MIT | 1.0 (May 2024) | Active | Block-triangular decomposition, 1-2 OOM speedup |
| **LiteRed** | Mathematica | Open | 2.x | Active (LiteRed2) | Heuristic symbolic reduction rules |
| **Reduze** | C++ | GPL-3.0 | 2.x (~2015) | Dormant | First MPI-distributed IBP tool |
| **FiniteFlow** | C++/Mathematica | Open | — | Active | General finite-field dataflow framework (backend) |
| **FireFly** | C++ | Open | — | Active | Standalone rational reconstruction library |
| **FORCER** | FORM | Open | — | Stable | Extremely fast for 4-loop massless propagators |

**Current best practice**: For the hardest problems, the community uses either **FIRE 7** or the **NeatIBP 1.1 + Kira 3** pipeline. Blade is emerging as a competitive alternative. The trend is toward syzygy-based methods that generate smaller systems, combined with finite-field arithmetic.

---

## 3. The Differential Equations Method

### Key Development Arc
1. **Kotikov (1991)**: Original observation that Feynman integrals satisfy ODEs in masses and momenta
2. **Remiddi (1997), Gehrmann & Remiddi (2000)**: Systematized for multi-leg two-loop calculations
3. **Henn (2013)**: The canonical/epsilon form revolution — choosing the right MI basis makes the DE system trivially solvable order-by-order in epsilon, with solutions in terms of iterated integrals
4. **Lee & Pomeransky (2013)**: Number of master integrals = number of critical points of the Lee-Pomeransky polynomial; released Mint package for automated counting

### Canonical Basis Finding Tools
- **CANONICA**: Mathematica, multi-scale algorithmic transformation
- **epsilon**: Lee's algorithm implementation
- **Fuchsia**: Open-source Python/Sage implementation

### Solution & Evaluation Tools
| Tool | Method | Strength |
|------|--------|----------|
| **AMFlow** (Liu & Ma) | Auxiliary mass flow, numerical ODE solving | Fully automatic, arbitrary precision |
| **DiffExp** (Hidding) | Series expansion along phase-space paths | Controlled precision, analytic continuation |
| **SeaSyde** | Series expansion | Handles complex masses |
| **pySecDec** | Sector decomposition + Monte Carlo | Fully numerical, no canonical form needed |
| **FIESTA5** | Sector decomposition, GPU-accelerated | Fast numerical validation |

### Function Classes
- **Multiple polylogarithms (MPLs)**: Cover most 2-loop cases with massless/single-mass kinematics
- **Elliptic MPLs**: Emerging at 2-loop with multiple masses; canonical DE formulation under active development (2025)
- **Calabi-Yau periods**: Appear at 3+ loops; the mathematical frontier

---

## 4. Intersection Theory: The New Paradigm

### Mathematical Framework
Feynman integrals in Baikov or Lee-Pomeransky representation are **twisted period integrals**: integrals of differential forms weighted by a multivalued "twist" function (product of propagator polynomials to non-integer powers). These live in a finite-dimensional **twisted cohomology group** whose dimension equals the number of master integrals.

The **intersection number** is a bilinear pairing between cohomology elements that enables direct projection of any integral onto a master integral basis — without generating or solving large linear systems.

### Development Arc

| Year | Milestone | Authors |
|------|-----------|---------|
| 2018 | First connection to scattering amplitudes | Mizera |
| 2019 | Extension to loop-level Feynman integrals | Mastrolia & Mizera |
| 2019 | Decomposition on maximal cuts; vector space structure | Frellesvig et al. |
| 2020-21 | Multivariate intersection numbers; three strategies | Frellesvig et al. |
| 2021-22 | Dual perspective via relative cohomology | Caron-Huot & Pokraka |
| 2022 | Macaulay matrix and Pfaffian systems from GKZ | Chestnov et al. |
| 2023 | Polynomial divisions, companion matrices, finite fields | Fontana & Peraro |
| 2024 | Delta-forms bypass analytic regulators; companion tensor algebra | Brunello et al. |
| 2025 | Feynman parametrization for intersection theory | Lu, Wang & Yang |
| 2026 | Branch representation reduces to (3L-3) variables | Huang, Ma, Wang & Yang |

### Intersection Theory vs IBP: Current Status
- **Advantage**: Direct projection (each MI coefficient computed independently), natural parallelism, no intermediate expression swell, automatic MI counting
- **Limitation**: As of 2026, IBP remains faster for most production calculations. Multivariate intersection number computation is expensive, scaling steeply with variable count.
- **The convergence**: Intersection theory provides structural insights (canonical bases, hidden relations) while finite-field IBP solvers handle brute-force reduction. The branch representation (arXiv:2604.05025) is narrowing the gap.
- **Software**: No general-purpose public package yet. Proof-of-concept implementations exist over finite fields (Fontana-Peraro 2023). The Padova group has internal codes for 2-loop 5-point problems.

### Baikov vs Lee-Pomeransky vs Feynman Parametrization
- **Baikov**: Variables are scalar products (inverse propagators). Dominant for intersection theory through 2023. Simple twist polynomial structure.
- **Lee-Pomeransky**: Feynman parameters with combined Symanzik polynomial. Natural connection to GKZ systems.
- **Feynman parametrization** (Lu, Wang & Yang 2025): Relative cohomology with boundary delta-forms avoids intermediate regulators. Simpler than Baikov for some topologies.
- **Branch representation** (Huang et al. 2024-2026): Groups Feynman parameters by shared quadratic loop-momentum structure ("branches"). Reduces variable count from O(N_propagators) to at most 3L-3.

---

## 5. The Branch Representation (The Paper Under Study)

### Core Idea (arXiv:2604.05025)
In an L-loop Feynman integral, propagators sharing the same quadratic form in loop momenta belong to the same **branch**. Introducing branch variables X_b = sum of Feynman parameters in branch b:

1. The integral factorizes into "fixed-branch integrals" (FBIs) that have **one-loop-like structure** and can be reduced almost for free
2. The remaining integration is over at most B ≤ 3L-3 branch variables
3. For intersection theory, this means computing at most (3L-3)-variable intersection numbers, **independent of the number of external legs**

### Results
- **Two-loop massive triangle** (6 propagators → normally 6 layers): Reduced to 3 layers. Runtime: 285s vs 10,785s in standard LP representation (**38x speedup**).
- **Two-loop pentabox** (8 propagators, 5 off-shell legs): Would need 11 layers in Baikov, 8 in LP — both infeasible. Branch representation: 3 layers, feasible computation. Linear systems are an order of magnitude smaller than Kira 3's IBP systems and have favorable block-triangular sparse structure.

### Significance
This is the first demonstration that intersection-theory-based reduction can be competitive with (and potentially surpass) state-of-the-art IBP methods for multi-leg integrals. The (3L-3) scaling is a game-changer for the HL-LHC program where 2-to-3 processes at NNLO are the frontier.

---

## 6. Emerging Directions

### AI/ML for Feynman Integrals
- **Song et al. (2025)**: ML models to predict IBP reduction coefficients, bypassing large linear system solving
- **Reinforcement learning** (2025): Optimizing IBP seeding/reduction strategies
- **Physics-informed neural networks** (2024): Fast evaluation of DE solutions
- **LLM + genetic algorithms** (2025): Explainable AI-assisted strategies

### Tropical Geometry
Borinsky, Panzer, and others have developed tropical methods for analyzing UV/IR divergence structure and providing new numerical integration strategies (tropical Monte Carlo).

### Symbol/Coproduct Methods
- Extended Steinmann relations and cluster algebras constrain symbol alphabets
- Bootstrap methods use these constraints to determine amplitudes without computing integrals
- D_n and G_2 cluster algebra structures organize multi-loop function spaces

### Beyond Polylogarithms
- Elliptic MPLs and iterated integrals of modular forms (2-loop with masses)
- Hyperelliptic (genus-2) periods emerging at 3 loops
- Calabi-Yau periods: the new mathematical frontier
- Canonical DE formulation for elliptic cases under active development (2025)

### Landau Singularities
Computational algebraic geometry methods (principal Landau determinant) now systematically classify integral singularities, tested on 114 diagrams including 2-loop 5-point non-planar QCD (2024).

---

## 7. Current Computational Frontiers

### Achieved Milestones (as of early 2026)
| Calculation | Status |
|-------------|--------|
| Two-loop five-point massless | Fully solved analytically (pentagon functions) |
| Two-loop five-point one-mass | Complete analytical MI set (2024) |
| Two-loop five-point two-mass (planar) | Computed |
| Three-loop five-point massless planar | All families completed analytically (late 2024) |
| Two-loop six-point massless | Alphabet (269 letters) identified; MIs in progress |
| Four-loop massless propagators | Largely solved |
| Five-loop QCD beta function | Completed |
| N3LO Higgs inclusive | Completed (Mistlberger 2018) |

### Active Frontiers
- Three-loop five-point non-planar (major open target)
- Three-loop five-point with masses (far beyond current capability)
- Four-loop four-point (under investigation)
- N3LO differential distributions for Higgs, Drell-Yan
- NNLO for all major 2→3 LHC processes

### HL-LHC Requirements
The High-Luminosity LHC physics program demands:
- NNLO predictions for all 2→3 processes (VVV, ttbar+V, VBF+jet)
- N3LO for key 2→1 and 2→2 processes
- Mixed QCD-EW corrections at NLO and beyond
- Improved PDF fits from higher-order DIS and Drell-Yan

---

## 8. Paper Library

All canonical papers are downloaded to `examples14/papers/`. Here is the complete catalog organized by topic:

### IBP Foundations & Algorithms
| File | Authors | Year | Topic |
|------|---------|------|-------|
| `hep-ph_0102032.pdf` | Laporta | 2001 | The Laporta algorithm |

### IBP Software
| File | Authors | Year | Tool |
|------|---------|------|------|
| `2311.02370.pdf` | Smirnov & Zeng | 2024 | FIRE 6.5 |
| `1201.4330.pdf` | von Manteuffel & Studerus | 2012 | Reduze 2 |
| `1310.1145.pdf` | Lee | 2014 | LiteRed |
| `2008.06494.pdf` | Klappert et al. | 2021 | Kira 2 |
| `2505.20197.pdf` | Lange et al. | 2025 | Kira 3 |
| `2305.08783.pdf` | Wu et al. | 2024 | NeatIBP |
| `2405.14621.pdf` | Guan et al. | 2024 | Blade |

### Intersection Theory
| File | Authors | Year | Topic |
|------|---------|------|-------|
| `1711.00469.pdf` | Mizera | 2018 | Intersection theory origins |
| `1810.03818.pdf` | Mastrolia & Mizera | 2019 | Intersection theory for Feynman integrals |
| `1901.11510.pdf` | Frellesvig et al. | 2019 | Decomposition on maximal cuts |
| `1907.02000.pdf` | Frellesvig et al. | 2019 | Vector space of Feynman integrals |
| `2104.06898.pdf` | Caron-Huot & Pokraka | 2021 | Duals of Feynman integrals I |
| `2112.00055.pdf` | Caron-Huot & Pokraka | 2022 | Duals of Feynman integrals II |
| `2204.12983.pdf` | Chestnov et al. | 2022 | Macaulay matrix approach |
| `2304.14336.pdf` | Fontana & Peraro | 2023 | Companion matrices, finite fields |
| `2401.01897.pdf` | Brunello et al. | 2024 | Improved intersection numbers |
| `2408.16668.pdf` | Brunello, Chestnov & Mastrolia | 2024 | Companion tensor algebra |

### Differential Equations & Evaluation
| File | Authors | Year | Topic |
|------|---------|------|-------|
| `1308.6676.pdf` | Lee & Pomeransky | 2013 | LP representation, MI counting |
| `1905.08019.pdf` | Peraro | 2019 | FiniteFlow framework |
| `2201.11669.pdf` | Liu & Ma | 2023 | AMFlow (auxiliary mass flow) |

### Branch Representation & Recent Advances
| File | Authors | Year | Topic |
|------|---------|------|-------|
| `2412.21053.pdf` | Huang, Huang & Ma | 2024 | Branch representation (original) |
| `2411.05226.pdf` | Lu, Wang & Yang | 2025 | Feynman param for intersection theory |
| `2502.09544.pdf` | Song et al. | 2025 | AI for integral reduction |

---

## 9. Assessment of arXiv:2604.05025

### Strengths
- The (3L-3) variable bound is a genuine theoretical advance with immediate practical consequences
- The 38x speedup on the triangle example is compelling, and the pentabox demonstration (infeasible → feasible) is the real headline
- Clean separation: FBI reduction handles the "easy" inner layer, intersection theory handles only the branch variables
- Block-triangular sparse structure of the resulting linear systems is a significant practical advantage

### Open Questions
- How does the method scale to 3+ loops? The bound 3L-3 = 6 at three loops is still manageable, but inner-layer dimensions will grow
- No public software release yet — the method uses an in-house FiniteFlow-based implementation
- Comparison with Kira 3 is indirect (linear system size rather than runtime)
- Performance on non-planar topologies and massive cases needs further investigation

### Bottom Line
This paper represents a significant step toward making intersection-theory-based reduction competitive with traditional IBP for real-world LHC calculations. The key insight — that branch variables decouple the leg-count dependence from the computational complexity — could be transformative if realized in optimized public software.

---

*Report based on research into 35 references from arXiv:2604.05025 plus additional sources discovered during investigation. 24 canonical papers archived in `examples14/papers/`.*
