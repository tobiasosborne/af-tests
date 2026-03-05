#!/tmp/cas-venv/bin/python3
"""
VERIFIER-7: Deep verification of node 1.7.2 (Tensor propagator).

Checks:
1. Factor of 2: I_{TT} = (1/4) int p^4 |h^{TT}|^2.
   Canonical form: I = (1/2) int h A h => A = p^4/2, G = 2/p^4.

2. TT projector Pi^{TT}_{ijkl} = (1/2)(P^T_{ik} P^T_{jl} + P^T_{il} P^T_{jk} - P^T_{ij} P^T_{kl})
   Check:
   a) Pi * Pi = Pi (idempotent)
   b) Pi is traceless in ij: Pi^{TT}_{iikl} = 0
   c) Pi is traceless in kl: Pi^{TT}_{ijkk} = 0
   d) Pi is transverse: k_i Pi^{TT}_{ijkl} = 0
   e) Pi is symmetric under (ij)<->(kl) and i<->j, k<->l
   f) Trace: Pi^{TT}_{ijij} = 2 (number of TT polarizations in 3D)
"""
import sys
from sympy import symbols, simplify, expand, eye, Matrix, Rational, KroneckerDelta

def main():
    print("=" * 60)
    print("VERIFIER-7: Node 1.7.2 — Tensor propagator deep check")
    print("=" * 60)
    print()

    # ========================================
    # Check 1: Factor of 2 in propagator
    # ========================================
    print("--- Check 1: Factor of 2 ---")
    print()
    print("The tensor action is I_{TT} = (1/4) int p^4 |h^{TT}_{ij}|^2")
    print()
    print("The normalization convention (from 6.3.1): the action is written as")
    print("I = int Phi* M Phi = (1/2) int Phi A Phi, so A = 2M.")
    print()
    print("For tensors: I_{TT} = (1/4) int p^4 h^{TT*}_{ij} h^{TT}_{ij}")
    print("           = (1/2) * (p^4/2) * h^{TT*}_{ij} h^{TT}_{ij}")
    print("So the 'M' here (per component pair) is p^4/4 in the sense")
    print("that |h|^2 = h^*_{ij} h_{ij} sums over all ij.")
    print()
    print("Actually, let's be more careful. For a SINGLE TT component h_{ij}:")
    print("The test_tensor_action.py showed that for plus polarization (h_{xx}=f, h_{yy}=-f),")
    print("R_{mu nu} R^{mu nu} = (1/2)(Box f)^2.")
    print()
    print("This means the action for one polarization is:")
    print("  I_+ = (1/2) int (Box f)^2 = (1/2) int f Box^2 f (after IBP)")
    print("In Fourier: I_+ = (1/2) p^4 |f|^2")
    print("So for one component f: A_f = p^4 (not p^4/2).")
    print("Wait, but the node says 'I_{TT} = (1/4) int p^4 |h^{TT}|^2'")
    print("where |h^{TT}|^2 = h^{TT*}_{ij} h^{TT}_{ij} sums over ALL ij.")
    print()
    print("For plus polarization: h^{TT}_{ij} h^{TT}_{ij} = f^2 + (-f)^2 = 2f^2")
    print("So (1/4) p^4 * 2|f|^2 = (1/2) p^4 |f|^2. CORRECT!")
    print()
    print("Now the propagator of the individual component f:")
    print("  I_+ = (1/2) p^4 |f|^2 => A = p^4, G_f = 1/p^4")
    print()
    print("But the propagator of h^{TT}_{ij} as a tensor field needs a projector:")
    print("  <h^{TT}_{ij} h^{TT}_{kl}> = G_component * Pi^{TT}_{ijkl}")
    print()
    print("What is G_component? The action in terms of the FULL tensor h^{TT}_{ij}:")
    print("  I_{TT} = (1/4) p^4 h^{TT*}_{ij} h^{TT}_{ij}")
    print("The normalization 6.3.1 says the propagator is (1/2) M^{-1}.")
    print("Here, the effective 'M per component' in the sense of")
    print("  I = M * h^{TT*}_{ij} h^{TT}_{ij}")
    print("gives M = p^4/4 per-component-pair. Wait no...")
    print()
    print("Let me think about this differently.")
    print("The action is I_{TT} = (1/4) int p^4 h^*_{ij} h_{ij}.")
    print("This is in the form I = int h^* M_tensor h where M_tensor acts as")
    print("  (M_tensor)_{ij,kl} = (p^4/4) delta_{ik} delta_{jl}")
    print("on the TT subspace (after projection).")
    print()
    print("Actually, the correct normalization: the field h^{TT}_{ij} is the")
    print("full tensor. The propagator is the inverse of the kinetic operator")
    print("on the TT subspace. The kinetic operator maps:")
    print("  h^{TT}_{ij} -> (p^4/4) * 2 * Pi^{TT}_{ijkl} h^{TT}_{kl}")
    print("Hmm, this is getting confusing. Let me use the consistency check approach.")
    print()

    # Direct check: consistency with the per-component calculation
    # For plus polarization: <f f> = 1/p^4 (from I_+ = (1/2) p^4 |f|^2)
    # h^{TT}_{xx} = f, h^{TT}_{yy} = -f
    # <h^{TT}_{xx} h^{TT}_{xx}> should = <f f> = 1/p^4
    # From the formula: <h^{TT}_{xx} h^{TT}_{xx}> = 2 Pi^{TT}_{xxxx} / p^4
    # So we need Pi^{TT}_{xxxx} = 1/2

    print("CONSISTENCY CHECK: For k along z, plus polarization:")
    print("  <h_{xx} h_{xx}> = 2 * Pi^{TT}_{xxxx} / p^4")
    print("  This should equal 1/p^4 (from per-component calc)")
    print("  So Pi^{TT}_{xxxx} should be 1/2.")
    print()

    # Compute Pi^{TT} for k along z
    # P^T = diag(1, 1, 0)
    PT = [[0]*3 for _ in range(3)]
    PT[0][0] = 1
    PT[1][1] = 1
    # PT[2][2] = 0 (k along z, so P^T_{zz} = 0)

    def Pi_TT(i, j, k, l):
        return Rational(1, 2) * (PT[i][k]*PT[j][l] + PT[i][l]*PT[j][k] - PT[i][j]*PT[k][l])

    # Check Pi^{TT}_{xxxx}
    val = Pi_TT(0, 0, 0, 0)
    print(f"  Pi^TT_xxxx = (1/2)(P^T_xx P^T_xx + P^T_xx P^T_xx - P^T_xx P^T_xx)")
    print(f"             = (1/2)(1 + 1 - 1) = 1/2")
    print(f"  Computed: {val}")
    assert val == Rational(1, 2), f"FAIL: expected 1/2, got {val}"
    print(f"  => <h_xx h_xx> = 2 * (1/2) / p^4 = 1/p^4. CORRECT!")
    print()

    # Check <h_{xx} h_{yy}> = 2 Pi^{TT}_{xxyy} / p^4
    # For plus polarization: h_{xx} = f, h_{yy} = -f
    # <h_{xx} h_{yy}> = <f * (-f)> = -<f f> = -1/p^4
    val_xxyy = Pi_TT(0, 0, 1, 1)
    print(f"  Pi^TT_xxyy = (1/2)(P^T_xy P^T_xy + P^T_xy P^T_xy - P^T_xx P^T_yy)")
    print(f"             = (1/2)(0 + 0 - 1*1) = -1/2")
    print(f"  Computed: {val_xxyy}")
    assert val_xxyy == Rational(-1, 2), f"FAIL: expected -1/2, got {val_xxyy}"
    print(f"  => <h_xx h_yy> = 2 * (-1/2) / p^4 = -1/p^4. CORRECT!")
    print()

    # ========================================
    # Check 2: Pi^{TT} properties
    # ========================================
    print("--- Check 2: TT projector properties ---")
    print()

    # 2a: Tracelessness in first pair (ij): Pi^{TT}_{iikl} = 0
    print("2a: Traceless in (ij)?")
    for k_idx in range(3):
        for l_idx in range(3):
            trace_ij = sum(Pi_TT(i, i, k_idx, l_idx) for i in range(3))
            if trace_ij != 0:
                print(f"  FAIL: Pi^TT_{{ii{k_idx}{l_idx}}} = {trace_ij}")
                assert False
    print("  PASS: Pi^{TT}_{iikl} = 0 for all k,l")
    print()

    # 2b: Traceless in second pair: Pi^{TT}_{ijkk} = 0
    print("2b: Traceless in (kl)?")
    for i_idx in range(3):
        for j_idx in range(3):
            trace_kl = sum(Pi_TT(i_idx, j_idx, k_idx, k_idx) for k_idx in range(3))
            if trace_kl != 0:
                print(f"  FAIL: Pi^TT_{{{i_idx}{j_idx}kk}} = {trace_kl}")
                assert False
    print("  PASS: Pi^{TT}_{ijkk} = 0 for all i,j")
    print()

    # 2c: Transversality: k_i Pi^{TT}_{ijkl} = 0
    # k along z, so k_i = (0, 0, k). Only z-component matters.
    print("2c: Transverse? k_i Pi^{TT}_{ijkl} = 0?")
    for j_idx in range(3):
        for k_idx in range(3):
            for l_idx in range(3):
                # k_i Pi_{ijkl} = k * Pi_{2,j,k,l} (only z-component of k)
                val = Pi_TT(2, j_idx, k_idx, l_idx)
                if val != 0:
                    print(f"  FAIL: Pi^TT_{{z,{j_idx},{k_idx},{l_idx}}} = {val}")
                    assert False
    print("  PASS: k_i Pi^{TT}_{ijkl} = 0 for all j,k,l")
    print()

    # 2d: Symmetry under i<->j
    print("2d: Symmetric in (ij)?")
    for i_idx in range(3):
        for j_idx in range(3):
            for k_idx in range(3):
                for l_idx in range(3):
                    diff_ij = Pi_TT(i_idx, j_idx, k_idx, l_idx) - Pi_TT(j_idx, i_idx, k_idx, l_idx)
                    if diff_ij != 0:
                        print(f"  FAIL at ({i_idx},{j_idx},{k_idx},{l_idx})")
                        assert False
    print("  PASS: Pi^{TT}_{ijkl} = Pi^{TT}_{jikl}")
    print()

    # 2e: Symmetry under (ij)<->(kl)
    print("2e: Symmetric under (ij)<->(kl)?")
    for i_idx in range(3):
        for j_idx in range(3):
            for k_idx in range(3):
                for l_idx in range(3):
                    diff_pair = Pi_TT(i_idx, j_idx, k_idx, l_idx) - Pi_TT(k_idx, l_idx, i_idx, j_idx)
                    if diff_pair != 0:
                        print(f"  FAIL at ({i_idx},{j_idx},{k_idx},{l_idx})")
                        assert False
    print("  PASS: Pi^{TT}_{ijkl} = Pi^{TT}_{klij}")
    print()

    # 2f: Idempotent: Pi * Pi = Pi
    print("2f: Idempotent? Pi * Pi = Pi?")
    for i_idx in range(3):
        for j_idx in range(3):
            for k_idx in range(3):
                for l_idx in range(3):
                    # (Pi * Pi)_{ijkl} = Pi_{ijmn} Pi_{mnkl}
                    product = sum(
                        Pi_TT(i_idx, j_idx, m, n) * Pi_TT(m, n, k_idx, l_idx)
                        for m in range(3) for n in range(3)
                    )
                    expected = Pi_TT(i_idx, j_idx, k_idx, l_idx)
                    if product != expected:
                        print(f"  FAIL at ({i_idx},{j_idx},{k_idx},{l_idx}): {product} != {expected}")
                        assert False
    print("  PASS: Pi^{TT}_{ijmn} Pi^{TT}_{mnkl} = Pi^{TT}_{ijkl}")
    print()

    # 2g: Trace: Pi^{TT}_{ijij} = number of TT DOF
    trace_full = sum(Pi_TT(i, j, i, j) for i in range(3) for j in range(3))
    print(f"2g: Trace Pi^TT_{{ijij}} = {trace_full}")
    # In 3D, TT symmetric tensors have 3*(3+1)/2 - 3 - 3 + 1 = 2 DOF
    # (6 symmetric - 3 transversality - 1 tracelessness = 2)
    # Wait: 6 - 3 (transverse) - 1 (traceless) = 2. Yes.
    assert trace_full == 2, f"FAIL: expected 2, got {trace_full}"
    print("  PASS: Tr = 2 (two TT polarizations, as expected in 3D)")
    print()

    # ========================================
    # Check 3: The factor of 2 in propagator
    # ========================================
    print("--- Check 3: Propagator factor of 2 ---")
    print()
    print("From the node: I_{TT} = (1/4) int p^4 h^{TT*}_{ij} h^{TT}_{ij}")
    print("The node identifies A/2 = p^4/4, so A = p^4/2, G = 2/p^4.")
    print()
    print("Let me verify this against the 'canonical normalization' of 6.3.1.")
    print("The action I = int Phi* M Phi, with A = 2M, G = A^{-1} = (1/2)M^{-1}.")
    print()
    print("For the tensor: I_{TT} = (1/4) int p^4 |h^{TT}|^2")
    print("This is I = M_{tensor} * |h^{TT}|^2 with M_{tensor} = p^4/4")
    print("  => A = 2 * M_{tensor} = p^4/2")
    print("  => G = 1/A = 2/p^4")
    print()
    print("Cross-check: <h_{xx} h_{xx}> = G * Pi^{TT}_{xxxx} = (2/p^4)(1/2) = 1/p^4")
    print("From direct calc: I_+ = (1/2) p^4 |f|^2 => <f f> = 1/p^4")
    print("Since h_{xx} = f, this checks out. CORRECT!")
    print()

    # ========================================
    # ADDITIONAL: Verify the vector propagator consistency
    # ========================================
    print("--- Cross-check: Vector propagator factor ---")
    print()
    print("From 6.3.3: I_V = (1/2) int k^2 p^2 |V_i|^2")
    print("This is already in the form (1/2) int V^* A V with A = k^2 p^2.")
    print("So G = 1/A = 1/(k^2 p^2). Correct (matches 6.4.2).")
    print()
    print("The tensor action has (1/4) not (1/2), which is why the extra")
    print("factor of 2 appears: G_{tensor} = 2/p^4 while G_{vector} = 1/(k^2 p^2).")
    print()

    # ========================================
    # VERDICT
    # ========================================
    print("=" * 60)
    print("VERDICT on 1.7.2:")
    print("  - The factor of 2 is CORRECT: I_{TT} = (1/4)p^4|h|^2 =>")
    print("    A = p^4/2, G = 2/p^4")
    print("  - The TT projector Pi^{TT}_{ijkl} is correctly defined")
    print("  - It satisfies: idempotent, traceless, transverse, symmetric")
    print("  - Trace = 2 (correct for 3D TT symmetric tensors)")
    print("  - Consistency check with per-polarization propagator passes")
    print()
    print("STATUS: PASS (no errors found)")
    print("=" * 60)

    return 0

if __name__ == "__main__":
    sys.exit(main())
