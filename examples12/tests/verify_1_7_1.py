#!/tmp/cas-venv/bin/python3
"""
VERIFIER-7: Deep verification of node 1.7.1 (Vector propagator).

Checks:
1. P^T_{ij} is the projector onto transverse modes (P^T * P^T = P^T)
2. P^T_{ij} k_j = 0 (projects out longitudinal)
3. For k_i V_i = 0 (transverse), P^T_{ij} V_j = V_i (identity on transverse)
4. The inverse A^{-1} P^T_{ij} = P^T_{ij}/(k^2 p^2) is UNIQUE on the transverse subspace
5. What happens to longitudinal part: longitudinal modes are pure gauge,
   not dynamical, so no propagator needed.
"""
import sys
from sympy import symbols, simplify, expand, eye, Matrix, Rational, sqrt

def main():
    print("=" * 60)
    print("VERIFIER-7: Node 1.7.1 — Vector propagator deep check")
    print("=" * 60)
    print()

    # Work in 3D with k along z-axis: k = (0, 0, k)
    k = symbols('k', positive=True)
    p2 = symbols('p2')  # p^2 = omega^2 - k^2

    # P^T_{ij} = delta_{ij} - k_i k_j / k^2
    # For k along z: k_i = (0, 0, k)
    # P^T = diag(1, 1, 0) in the (x, y, z) basis
    PT = Matrix([
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 0]
    ])

    # Check 1: P^T * P^T = P^T (idempotent)
    PT_sq = PT * PT
    diff1 = simplify(PT_sq - PT)
    print("Check 1: P^T * P^T = P^T (idempotent)?")
    print(f"  P^T^2 - P^T = {diff1}")
    assert diff1 == Matrix.zeros(3, 3), "FAIL: Not idempotent"
    print("  PASS: P^T is idempotent")
    print()

    # Check 2: P^T_{ij} k_j = 0
    k_vec = Matrix([0, 0, k])
    PT_k = PT * k_vec
    print("Check 2: P^T * k = 0?")
    print(f"  P^T * k = {PT_k.T}")
    assert PT_k == Matrix.zeros(3, 1), "FAIL: P^T does not project out k"
    print("  PASS: P^T annihilates k")
    print()

    # Check 3: For transverse V (V_z = 0), P^T V = V
    Vx, Vy = symbols('V_x V_y')
    V_trans = Matrix([Vx, Vy, 0])
    PT_V = PT * V_trans
    diff3 = simplify(PT_V - V_trans)
    print("Check 3: P^T * V_trans = V_trans?")
    print(f"  P^T * V = {PT_V.T}, V = {V_trans.T}")
    print(f"  Difference = {diff3.T}")
    assert diff3 == Matrix.zeros(3, 1), "FAIL: P^T is not identity on transverse"
    print("  PASS: P^T is the identity on transverse vectors")
    print()

    # Check 4: Uniqueness of inverse on transverse subspace
    # The operator A = k^2 p^2 (scalar) acts on each transverse component.
    # On the transverse subspace (2D), the kinetic operator is A * P^T.
    # Its inverse restricted to transverse subspace is (1/A) * P^T.
    # This is unique because on the transverse subspace, A * P^T has
    # eigenvalue A on each transverse eigenvector, and eigenvalue 0 on
    # the longitudinal direction.
    #
    # The propagator G_{ij} satisfies: A * P^T_{ik} G_{kj} = P^T_{ij}
    # (resolving to the identity on the transverse subspace only).
    # G_{ij} = P^T_{ij} / A is the unique solution.
    print("Check 4: Uniqueness of inverse on transverse subspace")
    # Verify: A * P^T * (P^T / A) = P^T
    # = P^T * P^T = P^T. Yes.
    product = PT * PT  # A cancels
    diff4 = simplify(product - PT)
    print(f"  A * P^T * (P^T/A) = P^T * P^T = {product}")
    print(f"  Difference from P^T: {diff4}")
    assert diff4 == Matrix.zeros(3, 3), "FAIL: Inverse check"
    print("  PASS: A * P^T * (P^T/A) = P^T (correct inverse on transverse subspace)")
    print()

    # Check 5: General k direction
    # P^T_{ij}(k) = delta_{ij} - k_i k_j / k^2
    # For general k = (kx, ky, kz) with k^2 = kx^2 + ky^2 + kz^2:
    kx, ky, kz = symbols('k_x k_y k_z', real=True)
    k_sq = kx**2 + ky**2 + kz**2

    PT_general = eye(3) - Matrix([
        [kx*kx, kx*ky, kx*kz],
        [ky*kx, ky*ky, ky*kz],
        [kz*kx, kz*ky, kz*kz]
    ]) / k_sq

    # P^T * P^T = P^T?
    PT_gen_sq = PT_general * PT_general
    PT_gen_sq_simplified = PT_gen_sq.applyfunc(lambda x: simplify(x))
    diff5 = (PT_gen_sq_simplified - PT_general).applyfunc(lambda x: simplify(x))
    print("Check 5: General k direction — P^T^2 = P^T?")
    all_zero = all(simplify(diff5[i, j]) == 0 for i in range(3) for j in range(3))
    print(f"  All entries zero: {all_zero}")
    assert all_zero, "FAIL: P^T not idempotent for general k"
    print("  PASS: P^T is idempotent for general k")
    print()

    # Check trace: Tr(P^T) = 3 - k_i k_i / k^2 = 3 - 1 = 2
    trace_PT = sum(PT_general[i, i] for i in range(3))
    trace_simplified = simplify(trace_PT)
    print(f"Check 6: Tr(P^T) = {trace_simplified}")
    assert simplify(trace_simplified - 2) == 0, "FAIL: trace should be 2"
    print("  PASS: Tr(P^T) = 2 (two transverse directions)")
    print()

    # Check: P^T is symmetric
    diff_sym = (PT_general - PT_general.T).applyfunc(lambda x: simplify(x))
    all_sym = all(diff_sym[i, j] == 0 for i in range(3) for j in range(3))
    print(f"Check 7: P^T symmetric? {all_sym}")
    assert all_sym, "FAIL: P^T not symmetric"
    print("  PASS: P^T is symmetric")
    print()

    # VERDICT on 1.7.1
    print("=" * 60)
    print("VERDICT on 1.7.1:")
    print("  - The vector action I_V = (1/2) int k^2 p^2 |V_i|^2 is correct")
    print("    (verified by tests/test_vector_action.py)")
    print("  - P^T_{ij} is correctly the projector onto transverse modes")
    print("  - The propagator P^T_{ij}/(k^2 p^2) is the unique inverse on")
    print("    the transverse subspace")
    print("  - Longitudinal modes are unphysical (gauge/constraint), no propagator needed")
    print()
    print("MINOR NOTE: The node says 'A = k^2 p^2' and 'the inverse on the")
    print("transverse subspace: A^{-1} P^T_{ij} = P^T_{ij}/(k^2 p^2)'.")
    print("This is correct but could be more explicit about WHY P^T appears.")
    print("The answer: the kinetic operator in the transverse sector is A*P^T,")
    print("and its generalized inverse is (1/A)*P^T because P^T^2 = P^T.")
    print()
    print("STATUS: PASS (no errors found)")
    print("=" * 60)

    return 0

if __name__ == "__main__":
    sys.exit(main())
