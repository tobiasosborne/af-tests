#!/tmp/cas-venv/bin/python3
"""
Verify Theorem 6.3: Scalar propagators via M^{-1}/2.

The propagators are:
    <Phi Phi> = M_22 / (2 det(M)) = 3/(4k^4) + 1/(2k^2 p^2) + (1-2beta)/(8(1-3beta) p^4)
    <psi psi> = M_11 / (2 det(M)) = (1-2beta) / (8(1-3beta) p^4)
    <Phi psi> = -M_12 / (2 det(M)) = -1/(4k^2 p^2) - (1-2beta)/(8(1-3beta) p^4)

We verify these by computing (1/2)*M^{-1} symbolically and comparing with the
partial fraction decompositions.
"""
import sys
from sympy import (symbols, expand, simplify, factor, Rational, Matrix,
                   apart, cancel, together, collect, fraction)

def main():
    beta, k, p = symbols('beta k p')

    # Matrix entries
    M11 = 2 * (1 - 2*beta) * k**4
    M12 = 4 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4
    M22 = 12 * (1 - 3*beta) * p**4 + 8 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4

    # Build the matrix and compute inverse
    M = Matrix([[M11, M12], [M12, M22]])
    det_M = 8 * (1 - 3*beta) * k**4 * p**4  # from Lemma 6.1

    print("=" * 60)
    print("TEST: Theorem 6.3 — Scalar propagators via M^{-1}/2")
    print("=" * 60)
    print()

    # --- Test <psi psi> = M_11 / (2 det(M)) ---
    psi_psi_raw = M11 / (2 * det_M)
    psi_psi_simplified = cancel(psi_psi_raw)
    psi_psi_target = (1 - 2*beta) / (8 * (1 - 3*beta) * p**4)

    diff_psipsi = simplify(psi_psi_simplified - psi_psi_target)
    print(f"<psi psi> raw   = {psi_psi_raw}")
    print(f"<psi psi> cancel = {psi_psi_simplified}")
    print(f"<psi psi> target = {psi_psi_target}")
    print(f"Difference       = {diff_psipsi}")
    assert diff_psipsi == 0, f"FAIL: <psi psi> difference = {diff_psipsi}"
    print("PASS: <psi psi> = (1-2beta)/(8(1-3beta) p^4)")
    print()

    # --- Test <Phi psi> = -M_12 / (2 det(M)) ---
    phi_psi_raw = -M12 / (2 * det_M)
    phi_psi_simplified = cancel(phi_psi_raw)

    phi_psi_target = -1 / (4 * k**2 * p**2) - (1 - 2*beta) / (8 * (1 - 3*beta) * p**4)

    # Combine target over common denominator for comparison
    diff_phipsi = simplify(phi_psi_simplified - phi_psi_target)
    print(f"<Phi psi> raw    = {phi_psi_raw}")
    print(f"<Phi psi> cancel = {phi_psi_simplified}")
    print(f"<Phi psi> target = {phi_psi_target}")
    print(f"Difference        = {diff_phipsi}")
    assert diff_phipsi == 0, f"FAIL: <Phi psi> difference = {diff_phipsi}"
    print("PASS: <Phi psi> = -1/(4k^2 p^2) - (1-2beta)/(8(1-3beta) p^4)")
    print()

    # --- Test <Phi Phi> = M_22 / (2 det(M)) ---
    phi_phi_raw = M22 / (2 * det_M)
    phi_phi_simplified = cancel(phi_phi_raw)

    phi_phi_target = (Rational(3, 1) / (4 * k**4)
                      + 1 / (2 * k**2 * p**2)
                      + (1 - 2*beta) / (8 * (1 - 3*beta) * p**4))

    diff_phiphi = simplify(phi_phi_simplified - phi_phi_target)
    print(f"<Phi Phi> raw    = {phi_phi_raw}")
    print(f"<Phi Phi> cancel = {phi_phi_simplified}")
    print(f"<Phi Phi> target = {phi_phi_target}")
    print(f"Difference        = {diff_phiphi}")
    assert diff_phiphi == 0, f"FAIL: <Phi Phi> difference = {diff_phiphi}"
    print("PASS: <Phi Phi> = 3/(4k^4) + 1/(2k^2 p^2) + (1-2beta)/(8(1-3beta) p^4)")
    print()

    # --- Verify partial fractions in p^2 ---
    # Treat k as a parameter, decompose in p
    print("--- Partial fraction decomposition checks ---")
    print()

    # For <Phi Phi>, do partial fractions in p^2 by substituting q = p^2
    q = symbols('q', positive=True)
    phi_phi_in_q = phi_phi_simplified.subs(p**2, q).subs(p**4, q**2)
    pf_phiphi = apart(phi_phi_in_q, q)
    print(f"<Phi Phi> partial fracs in q=p^2: {pf_phiphi}")
    print()

    # --- Cross-check: M * M^{-1} = I ---
    M_inv_times_2 = Matrix([
        [phi_phi_simplified, phi_psi_simplified],
        [phi_psi_simplified, psi_psi_simplified]
    ])
    # M * (M^{-1}/2) * 2 = I, so M * M_inv_times_2 * 2 should be I... wait
    # Actually (1/2)*M^{-1} means M * ((1/2)M^{-1}) = (1/2)*I
    # So 2 * M * (1/2 M^{-1}) = I
    product = 2 * M * M_inv_times_2
    product_simplified = product.applyfunc(cancel)
    print(f"2 * M * (M^{{-1}}/2) = {product_simplified}")
    identity = Matrix([[1, 0], [0, 1]])
    for i in range(2):
        for j in range(2):
            diff_ij = simplify(product_simplified[i, j] - identity[i, j])
            assert diff_ij == 0, f"FAIL: (2*M*(M^-1/2))[{i},{j}] = {product_simplified[i,j]}, expected {identity[i,j]}"
    print("PASS: 2 * M * (M^{-1}/2) = I (matrix identity verified)")
    print()

    print("ALL TESTS PASSED")
    return 0

if __name__ == "__main__":
    sys.exit(main())
