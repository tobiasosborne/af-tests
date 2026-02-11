# Quantum Group Generalization of BLM Model — Proof Tree

## Overview

This directory contains an adversarial proof tree (using the `af` tool) for the
**quantum group generalization** of the Biggs-Lin-Maldacena melonic quantum mechanical
model (arXiv:2601.08908).

## Main Conjecture

Replacing SU(2) Wigner 3j symbols with U_q(su(2)) quantum Clebsch-Gordan coefficients
in the BLM supercharge yields a well-defined q-deformed Hamiltonian H_q = {Q_q, Q_q†}
that:

1. **Preserves N=2 SUSY** and positive semi-definiteness (q > 0 real)
2. **Exhibits melonic dominance** at large j via quantum 3j orthogonality
3. **Admits q-BPS states** with count computable from q-Witten index
4. **Connects to Turaev-Viro** 3D topological invariants (generalizing Ponzano-Regge)

## Proof Structure (23 nodes)

```
1. Main conjecture
├── 1.1 Well-definedness and SUSY
│   ├── 1.1.1 Quantum 3j antisymmetry
│   ├── 1.1.2 Nilpotency Q_q² = 0
│   ├── 1.1.3 U_q(su(2)) covariance
│   └── 1.1.4 Positive semi-definiteness
├── 1.2 Melonic dominance
│   ├── 1.2.1 Quantum 3j bubble identity
│   ├── 1.2.2 q-melonic self-energy
│   ├── 1.2.3 Non-melonic suppression (q-tetrahedron)
│   ├── 1.2.4 q-9j vanishing
│   └── 1.2.5 q-12j leading correction
├── 1.3 q-BPS states and q-Witten index
│   ├── 1.3.1 q-Witten index computation (q-INDEPENDENT)
│   ├── 1.3.2 q-BPS at maximal spin
│   ├── 1.3.3 q-deformed BPS partition function
│   └── 1.3.4 Spectral deformation
└── 1.4 Turaev-Viro connection
    ├── 1.4.1 Ponzano-Regge review (q=1)
    ├── 1.4.2 Quantum 6j asymptotics (generic q)
    ├── 1.4.3 Root-of-unity truncation (Turaev-Viro)
    ├── 1.4.4 Chern-Simons correspondence
    └── 1.4.5 Physical interpretation
```

## Key Insight: What Survives q-Deformation

| Feature | q=1 (BLM) | Generic q>0 | q = root of unity |
|---------|-----------|-------------|-------------------|
| SUSY | N=2 | N=2 | N=2 |
| H >= 0 | Yes | Yes | Yes |
| Melonic dominance | Yes | Yes | Yes (truncated spins) |
| BPS count | 2×3^j | 2×3^j (topological) | Truncated by j_max |
| Gravity dual | Ponzano-Regge (3D EG) | Deformed Regge | Turaev-Viro (3D CS) |
| Witten index | q-independent | q-independent | q-independent |

## Usage

```bash
cd quantum_group_proof/
af status          # View proof tree
af jobs            # See available work
af get 1.2.1       # Get details of a specific node
af export -o out.md  # Export full proof
```

## Definitions

- `quantum-3j-symbol`: q-analog of Wigner 3j for U_q(su(2))
- `q-supercharge`: Q_q with quantum 3j couplings
- `q-hamiltonian`: H_q = {Q_q, Q_q†}
- `quantum-6j-symbol`: q-analog of Racah-Wigner 6j
- `melonic-dominance`: Dominance of bubble-reducible diagrams at large j

## External References

- BLM paper (arXiv:2601.08908)
- Turaev-Viro (Topology 1992)
- Kassel, Quantum Groups (Springer GTM 155)

## Next Steps

1. **Verifier pass**: Challenge each leaf node for rigor
2. **Numerics**: Implement q-deformed Hamiltonian (modify existing Julia code)
3. **Deeper refinement**: Leaf nodes 1.2.3-1.2.5 need explicit asymptotic calculations
4. **Root-of-unity subtleties**: Node 1.4.3 needs careful treatment of truncation
