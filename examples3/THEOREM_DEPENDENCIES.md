# Theorem Dependency Graph

> Critical path analysis for parallel agentic development

---

## 1. Main Theorems (Numbered by Thesis)

### Chapter 1: Normal Forms
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 1.2 | Doubly stochastic normal form (classical) | — | 100 |
| 1.8 | Irreducibility equivalences | 1.2 | 80 |
| 1.11 | E(1) > 0 equivalences | — | 60 |
| 1.14 | Sufficient conditions (weak) | 1.11, Brouwer | 100 |
| 1.15 | Sufficient conditions (strong) | 1.14 | 150 |
| 1.18 | DS ⟹ sum of irreducibles | 1.8 | 80 |
| 1.21 | Kernel-reducing ⟹ irreducible | 1.8 | 70 |
| 1.25 | Kernel-reducing ⟺ fully indecomposable | 1.21 | 60 |
| 1.26 | **Conjecture** (not proven) | — | — |

### Chapter 2: Fixed Points & Jordan Basics
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 2.6 | Subsequence limit for T_φ | Spectral theory | 80 |
| 2.7 | Basic fixed point properties | — | 60 |
| 2.12 | Special JA is semisimple | JA basics | 50 |
| **2.13** | **Classification of formally real JAs** | JA basics | 400 |
| 2.17 | Jordan triple product | JA basics | 30 |
| 2.18 | (M_d)_h is formally real | 2.13 | 40 |
| 2.23 | 2-positive ⟹ Schwarz | CP maps | 80 |
| 2.24 | Jordan-Schwarz inequality | Kadison | 100 |
| 2.25 | Equality propagation | 2.24 | 80 |
| **2.26** | **F_{T*} is Jordan algebra** | 2.24, 2.25, 2.12 | 150 |
| 2.27 | Without full-rank fixed point | 2.26 | 100 |

### Chapter 3: Representation Theory
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 3.5 | Quaternion decomposition | — | 40 |
| 3.6 | Quaternion embedding | 3.5 | 120 |
| 3.7 | Spin factor embedding (even) | Clifford | 100 |
| 3.8 | Spin factor embedding (odd) | 3.7 | 80 |
| 3.10 | Universal envelope existence | Free algebra | 150 |
| 3.11 | Direct sum decomposition | 3.10 | 80 |
| 3.12 | Universal property extension | 3.10 | 100 |
| 3.14 | Simple envelope dimension | 3.12 | 80 |
| **3.15** | **Skolem-Noether** | Central simple | 250 |
| 3.17 | Unitary equivalence | 3.15 | 100 |
| 3.22 | Spin factor envelope | 3.7, 3.8 | 120 |
| **3.23** | **Artin-Wedderburn** | Ring theory | 350 |
| **3.3** | **Classification of complex JAs** | 2.13, 3.6-3.8, 3.15, 3.23 | 300 |
| 3.4 | Reversibility characterization | 3.3 | 150 |

### Chapter 4: Projections
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 4.3 | Uniqueness (TP projection) | 2.26 | 100 |
| 4.4 | Direct sum projection | 4.3 | 80 |
| 4.5 | Spin factor projection existence | 3.3, 4.3 | 150 |
| 4.10 | Conditional expectation char. | 4.3 | 120 |
| 4.14 | Spin factor projection formula | 4.5 | 200 |
| 4.17 | Reversible projection existence | 3.4, 4.3 | 150 |
| 4.20 | Reversible projection formula | 4.17 | 200 |

### Chapter 5: Characterization
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 5.1 | Decomposability criterion | Ch 4, Decomposable def | 100 |
| 5.3 | Spin factor indecomposability | 4.14, 5.1 | 150 |
| 5.5 | Atomic projection char. | 5.3 | 120 |

### Chapter 6: Trace-Preserving & Peripheral
| ID | Theorem | Dependencies | Est. LOC |
|----|---------|--------------|----------|
| 6.1 | TP fixed points are JAs | 2.26 | 150 |
| 6.3 | Peripheral eigenspace structure | Spectral | 100 |
| 6.5 | Peripheral spectrum is group | 6.3 | 120 |
| 6.8 | CP case simplification | 6.1, CP maps | 80 |

---

## 2. Dependency Graph (ASCII)

```
                    ┌──────────────────────────────────────────────────────────────┐
                    │                         FOUNDATIONS                           │
                    └──────────────────────────────────────────────────────────────┘
                                                    │
        ┌───────────────────────────────────────────┼───────────────────────────────────────────┐
        │                                           │                                           │
        ▼                                           ▼                                           ▼
┌───────────────┐                          ┌───────────────┐                          ┌───────────────┐
│ Positive Maps │                          │ Jordan Basics │                          │ Free Algebras │
│   (1.11)      │                          │   (2.7)       │                          │   (mathlib)   │
└───────┬───────┘                          └───────┬───────┘                          └───────┬───────┘
        │                                          │                                          │
        │                              ┌───────────┴───────────┐                              │
        │                              │                       │                              │
        ▼                              ▼                       ▼                              ▼
┌───────────────┐              ┌───────────────┐       ┌───────────────┐              ┌───────────────┐
│ Schwarz Ineq  │              │ Formally Real │       │  Spin Factor  │              │ Universal Env │
│  (2.23-2.25)  │              │    (2.13)     │       │   (2.14)      │              │    (3.10)     │
└───────┬───────┘              └───────┬───────┘       └───────┬───────┘              └───────┬───────┘
        │                              │                       │                              │
        │                              └───────────┬───────────┘                              │
        │                                          │                                          │
        ▼                                          ▼                                          ▼
┌───────────────┐                          ┌───────────────┐                          ┌───────────────┐
│  F_{T*} is JA │                          │ JA Embeddings │                          │ Skolem-Noether│
│    (2.26)     │◄─────────────────────────│  (3.6-3.8)    │                          │    (3.15)     │
└───────┬───────┘                          └───────┬───────┘                          └───────┬───────┘
        │                                          │                                          │
        │                                          ▼                                          ▼
        │                                  ┌───────────────┐                          ┌───────────────┐
        │                                  │Artin-Wedderburn                          │ JA Classif.   │
        │                                  │    (3.23)     │─────────────────────────▶│    (3.3)      │
        │                                  └───────────────┘                          └───────┬───────┘
        │                                                                                     │
        │                                          ┌──────────────────────────────────────────┘
        │                                          │
        ▼                                          ▼
┌───────────────┐                          ┌───────────────┐
│  Uniqueness   │◄─────────────────────────│ Reversibility │
│    (4.3)      │                          │    (3.4)      │
└───────┬───────┘                          └───────┬───────┘
        │                                          │
        ├──────────────────────────────────────────┤
        │                                          │
        ▼                                          ▼
┌───────────────┐                          ┌───────────────┐
│ Spin Proj     │                          │ Reversible    │
│ (4.5, 4.14)   │                          │ Proj (4.17)   │
└───────┬───────┘                          └───────┬───────┘
        │                                          │
        └────────────────────┬─────────────────────┘
                             │
                             ▼
                    ┌───────────────┐
                    │ Decomposable  │
                    │    (Ch 5)     │
                    └───────────────┘
```

---

## 3. Critical Path

The **critical path** determines minimum time:

```
Jordan Basics → Formally Real (2.13) → Spin Factor → Embeddings (3.6-3.8)
                                                            │
                     ┌──────────────────────────────────────┘
                     ▼
            Universal Envelope (3.10) → Skolem-Noether (3.15)
                                                │
                     ┌──────────────────────────┘
                     ▼
            Artin-Wedderburn (3.23) → Classification (3.3)
                                                │
                     ┌──────────────────────────┘
                     ▼
            Reversibility (3.4) → Projections (Ch 4)
```

**Critical path LOC**: ~2,500 LOC
**At 2K LOC/day**: ~1.5 days minimum for critical path

---

## 4. Parallel Development Tracks

### Track A: Jordan Algebra Theory
```
Jordan/Basic.lean (Day 1)
    ↓
Jordan/FormallyReal.lean (Day 1)
    ↓
Jordan/SpinFactor/Def.lean (Day 1)
    ↓
Jordan/Classification.lean (Day 2)
```

### Track B: Positive Maps & Schwarz
```
Basic/PositiveMap.lean (Day 1)
    ↓
Basic/Schwarz.lean (Day 1)
    ↓
Basic/Kadison.lean (Day 1)
    ↓
FixedPoint/JordanStructure.lean (Day 2)
```

### Track C: Embeddings & Structure Theorems
```
Representation/Embedding/Quaternion.lean (Day 1)
    ↓
Representation/Embedding/SpinFactor.lean (Day 1)
    ↓
Representation/SkolemNoether.lean (Day 2)
    ↓
Representation/ArtinWedderburn.lean (Day 2)
```

### Track D: Normal Forms (Independent)
```
NormalForm/FullyIndecomposable.lean (Day 1)
    ↓
NormalForm/MenonOperator.lean (Day 1)
    ↓
NormalForm/Theorem.lean (Day 2)
```

**With 4 parallel tracks**: ~2 days for bulk of work

---

## 5. Agent Assignment Suggestion

| Agent | Focus | Files | Day |
|-------|-------|-------|-----|
| Agent 1 | Jordan infrastructure | Jordan/*.lean | 1-2 |
| Agent 2 | Positive maps + Schwarz | Basic/*.lean, FixedPoint/JordanStructure | 1-2 |
| Agent 3 | Embeddings | Representation/Embedding/*.lean | 1-2 |
| Agent 4 | Normal forms | NormalForm/*.lean | 1-2 |
| Agent 5 | Structure theorems | SkolemNoether, ArtinWedderburn | 2-3 |
| Agent 6 | Projections | Projection/*.lean | 3-4 |
| Agent 7 | Integration | Classification, Main | 4-5 |

---

## 6. Risk Points (Blocking Dependencies)

### High Risk Bottlenecks

1. **Theorem 2.13 (Classification)**
   - Blocks: All of Chapter 3
   - Mitigation: Start immediately, use existing Clifford

2. **Theorem 3.15 (Skolem-Noether)**
   - Blocks: Classification 3.3
   - Mitigation: Can use concrete matrix version first

3. **Theorem 3.23 (Artin-Wedderburn)**
   - Blocks: Classification 3.3
   - Mitigation: Complex case is easier (division algebras = ℂ)

4. **Chapter 4 Projections**
   - Blocks: Chapter 5 characterizations
   - Mitigation: Can parallelize spin vs reversible

### Low Risk (Independent)

- Chapter 1 (Normal forms) - fully independent
- Chapter 6 (Peripheral spectrum) - mostly independent after 2.26
- Appendix A - independent technical lemmas

---

## 7. Verification Points

After completing each phase, verify:

### Phase 1 Verification
- [ ] `lake build` succeeds
- [ ] Jordan product is associative (Prop 2.11)
- [ ] Spin factor satisfies Jordan identity

### Phase 2 Verification
- [ ] Schwarz inequality proven
- [ ] F_{T*} is a Jordan algebra (Thm 2.26)

### Phase 3 Verification
- [ ] Spin factor embeds correctly
- [ ] Universal envelope has universal property

### Phase 4 Verification
- [ ] Classification theorem (3.3) complete
- [ ] Projections exist and are unique

### Final Verification
- [ ] All sorries eliminated
- [ ] `#check` on main theorems
- [ ] Example computations work

---

## 8. Theorem Statements (Reference)

### Theorem 2.13 (Classification of Formally Real Jordan Algebras)
Every simple formally real Jordan algebra is isomorphic to one of:
1. (M_d(ℝ))_h - Real symmetric matrices
2. (M_d(ℂ))_h - Complex Hermitian matrices
3. (M_d(ℍ))_h - Quaternionic Hermitian matrices
4. V_n - Spin factors (ℝ1 + ℝⁿ)
5. H₃(𝕆) - Albert algebra (exceptional, 27-dim)

### Theorem 2.26 (Fixed Points are Jordan Algebras)
If T: M_d → M_d is positive with T(ρ) = ρ for some ρ > 0, then F_{T*} is a semi-simple unital Jordan algebra.

### Theorem 3.3 (Classification of Complex Jordan Subalgebras)
Every unital Jordan subalgebra J ⊂ M_d is (up to isomorphism) of the form:
```
J = (⊕ᵢ M_{dᵢ} ⊗ 1_{mᵢ}) ⊕ (⊕ᵢ J^C_{d̃ᵢ}) ⊕ (⊕ᵢ J^T_{d'ᵢ} ⊗ 1_{m'ᵢ})
  ⊕ (⊕ᵢ J^H_{d''ᵢ} ⊗ 1_{m''ᵢ}) ⊕ (⊕ᵢ Jspin^full_{kᵢ} ⊗ 1_{m'''ᵢ}) ⊕ (⊕ᵢ Jspin^sum_{kᵢ})
```

### Theorem 3.15 (Skolem-Noether)
Every automorphism of a finite-dimensional central-simple algebra over ℂ is inner: φ(A) = SAS⁻¹ for some invertible S.

### Theorem 3.23 (Artin-Wedderburn)
Every semisimple finite-dimensional algebra over ℂ is isomorphic to a product of matrix algebras: A ≅ ⊕ᵢ M_{nᵢ}(ℂ).

---

*Dependency analysis for strategic development planning.*
