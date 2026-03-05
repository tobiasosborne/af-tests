#!/tmp/cas-venv/bin/python3
"""
Verify Remark 7.2: Special values of beta.

At beta = 1/2:
    <psi psi> = 0  (numerator 1 - 2*beta = 0)
    <Phi psi> = -1/(4 k^2 p^2)  (p^{-4} piece vanishes)
    <Phi Phi> = 3/(4 k^4) + 1/(2 k^2 p^2)  (p^{-4} piece vanishes)

At beta = 1/3:
    det(M) = 0  (conformal gravity point, degenerate)
"""
import sys
from sympy import symbols, simplify, Rational, cancel, expand, oo, limit

def main():
    beta, k, p = symbols('beta k p')

    print("=" * 60)
    print("TEST: Remark 7.2 — Special values of beta")
    print("=" * 60)
    print()

    # Matrix entries (from Lemma 6.1)
    M11 = 2 * (1 - 2*beta) * k**4
    M12 = 4 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4
    M22 = 12 * (1 - 3*beta) * p**4 + 8 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4
    det_M = 8 * (1 - 3*beta) * k**4 * p**4

    # General propagators
    psi_psi = M11 / (2 * det_M)
    phi_psi = -M12 / (2 * det_M)
    phi_phi = M22 / (2 * det_M)

    # ========================================
    # Case 1: beta = 1/2
    # ========================================
    print("--- Case beta = 1/2 ---")
    print()
    b_half = Rational(1, 2)

    # <psi psi> at beta = 1/2
    # Numerator: M11 = 2*(1-1)*k^4 = 0
    M11_half = M11.subs(beta, b_half)
    print(f"M_11 at beta=1/2: {M11_half}")
    assert M11_half == 0, f"FAIL: M_11 should be 0, got {M11_half}"
    print("PASS: M_11 = 0 at beta=1/2 => <psi psi> = 0")
    print()

    # det(M) at beta = 1/2
    det_half = det_M.subs(beta, b_half)
    print(f"det(M) at beta=1/2: {det_half}")
    expected_det_half = 8 * (1 - Rational(3,2)) * k**4 * p**4
    assert simplify(det_half - expected_det_half) == 0
    print(f"det(M) = {expand(det_half)} = -4 k^4 p^4")
    assert simplify(det_half + 4*k**4*p**4) == 0, "FAIL: det at beta=1/2"
    print("PASS: det(M) = -4 k^4 p^4 at beta=1/2")
    print()

    # <Phi psi> at beta = 1/2
    M12_half = M12.subs(beta, b_half)
    phi_psi_half = cancel(-M12_half / (2 * det_half))
    target_phi_psi_half = -1 / (4 * k**2 * p**2)
    diff_phi_psi = simplify(phi_psi_half - target_phi_psi_half)
    print(f"M_12 at beta=1/2: {expand(M12_half)}")
    print(f"<Phi psi> at beta=1/2: {phi_psi_half}")
    print(f"Target: -1/(4 k^2 p^2)")
    print(f"Difference: {diff_phi_psi}")
    assert diff_phi_psi == 0, f"FAIL: <Phi psi> at beta=1/2, diff = {diff_phi_psi}"
    print("PASS: <Phi psi> = -1/(4 k^2 p^2) at beta=1/2  (p^{-4} piece vanishes)")
    print()

    # <Phi Phi> at beta = 1/2
    M22_half = M22.subs(beta, b_half)
    phi_phi_half = cancel(M22_half / (2 * det_half))
    target_phi_phi_half = Rational(3, 4) / k**4 + Rational(1, 2) / (k**2 * p**2)
    diff_phi_phi = simplify(phi_phi_half - target_phi_phi_half)
    print(f"M_22 at beta=1/2: {expand(M22_half)}")
    print(f"<Phi Phi> at beta=1/2: {phi_phi_half}")
    print(f"Target: 3/(4k^4) + 1/(2k^2 p^2)")
    print(f"Difference: {diff_phi_phi}")
    assert diff_phi_phi == 0, f"FAIL: <Phi Phi> at beta=1/2, diff = {diff_phi_phi}"
    print("PASS: <Phi Phi> = 3/(4k^4) + 1/(2k^2 p^2) at beta=1/2  (p^{-4} piece vanishes)")
    print()

    # Verify the p^{-4} coefficient is proportional to (1-2*beta) generically
    psi_psi_generic = cancel(psi_psi)
    print(f"<psi psi> generic = {psi_psi_generic}")
    # The p^{-4} term in all propagators has coefficient (1-2*beta)/(8(1-3*beta))
    # which vanishes at beta = 1/2.
    coeff_p4 = (1 - 2*beta) / (8 * (1 - 3*beta))
    coeff_at_half = coeff_p4.subs(beta, b_half)
    print(f"p^{{-4}} coefficient = (1-2beta)/(8(1-3beta)), at beta=1/2: {coeff_at_half}")
    assert coeff_at_half == 0
    print("PASS: p^{-4} coefficient vanishes at beta=1/2")
    print()

    # ========================================
    # Case 2: beta = 1/3 (conformal gravity)
    # ========================================
    print("--- Case beta = 1/3 (conformal gravity) ---")
    print()
    b_third = Rational(1, 3)

    det_third = det_M.subs(beta, b_third)
    print(f"det(M) at beta=1/3: {det_third}")
    assert det_third == 0, f"FAIL: det should be 0, got {det_third}"
    print("PASS: det(M) = 0 at beta=1/3 (conformal gravity point)")
    print()

    # Also check: (1 - 3*beta) vanishes
    factor_check = (1 - 3*b_third)
    assert factor_check == 0
    print("PASS: (1 - 3*beta) = 0 at beta=1/3")
    print()

    # The matrix M at beta=1/3
    M11_third = M11.subs(beta, b_third)
    M12_third = M12.subs(beta, b_third)
    M22_third = M22.subs(beta, b_third)
    print(f"M_11 at beta=1/3: {expand(M11_third)}")
    print(f"M_12 at beta=1/3: {expand(M12_third)}")
    print(f"M_22 at beta=1/3: {expand(M22_third)}")
    # M becomes proportional to k^4 times [[1,1],[1,1]] (rank 1)
    # M_11 = 2*(1/3)*k^4 = (2/3)*k^4
    # M_12 = 0 + (2/3)*k^4 = (2/3)*k^4
    # M_22 = 0 + 0 + (2/3)*k^4 = (2/3)*k^4
    assert simplify(M11_third - Rational(2,3)*k**4) == 0
    assert simplify(M12_third - Rational(2,3)*k**4) == 0
    assert simplify(M22_third - Rational(2,3)*k**4) == 0
    print("PASS: M = (2/3)k^4 * [[1,1],[1,1]] at beta=1/3 (rank 1)")
    print()

    # ========================================
    # Case 3: beta = 0 (pure R_{mu nu}^2 gravity)
    # ========================================
    print("--- Case beta = 0 (R_{mu nu}^2 gravity) ---")
    print()
    b_zero = 0

    det_zero = det_M.subs(beta, b_zero)
    print(f"det(M) at beta=0: {expand(det_zero)}")
    assert simplify(det_zero - 8*k**4*p**4) == 0
    print("PASS: det(M) = 8 k^4 p^4 at beta=0")

    phi_phi_zero = cancel(M22.subs(beta, b_zero) / (2 * det_zero))
    target_zero = Rational(3, 4)/k**4 + Rational(1, 2)/(k**2*p**2) + Rational(1, 8)/p**4
    diff_zero = simplify(phi_phi_zero - target_zero)
    print(f"<Phi Phi> at beta=0: {phi_phi_zero}")
    print(f"Target: 3/(4k^4) + 1/(2k^2 p^2) + 1/(8p^4)")
    print(f"Difference: {diff_zero}")
    assert diff_zero == 0, f"FAIL: <Phi Phi> at beta=0"
    print("PASS: <Phi Phi> correct at beta=0")
    print()

    # ========================================
    # Verify beta-dependence is only through (1-2beta)/(1-3beta)
    # ========================================
    print("--- Beta-dependence structure ---")
    print()
    # All propagators can be written as:
    # <Phi Phi> = 3/(4k^4) + 1/(2k^2 p^2) + alpha(beta)/p^4
    # <Phi psi> = -1/(4k^2 p^2) - alpha(beta)/p^4
    # <psi psi> = alpha(beta)/p^4
    # where alpha(beta) = (1-2beta)/(8(1-3beta))

    alpha = (1 - 2*beta) / (8 * (1 - 3*beta))

    phi_phi_general = Rational(3,4)/k**4 + Rational(1,2)/(k**2*p**2) + alpha/p**4
    phi_psi_general = Rational(-1,4)/(k**2*p**2) - alpha/p**4
    psi_psi_general = alpha/p**4

    diff_pp = simplify(cancel(phi_phi) - phi_phi_general)
    diff_ps = simplify(cancel(phi_psi) - phi_psi_general)
    diff_ss = simplify(cancel(psi_psi) - psi_psi_general)

    print(f"<Phi Phi> - general form: {diff_pp}")
    print(f"<Phi psi> - general form: {diff_ps}")
    print(f"<psi psi> - general form: {diff_ss}")
    assert diff_pp == 0, f"FAIL: <Phi Phi> structure"
    assert diff_ps == 0, f"FAIL: <Phi psi> structure"
    assert diff_ss == 0, f"FAIL: <psi psi> structure"
    print("PASS: All propagators have the correct alpha(beta) = (1-2beta)/(8(1-3beta)) structure")
    print()

    # Check: sum rule <Phi Phi> + 2<Phi psi> + <psi psi> = 3/(4k^4)
    total = simplify(cancel(phi_phi + 2*phi_psi + psi_psi))
    target_sum = Rational(3, 4) / k**4
    diff_sum = simplify(total - target_sum)
    print(f"<Phi Phi> + 2<Phi psi> + <psi psi> = {total}")
    print(f"Target: 3/(4k^4)")
    print(f"Difference: {diff_sum}")
    assert diff_sum == 0, f"FAIL: sum rule"
    print("PASS: Sum rule <Phi Phi> + 2<Phi psi> + <psi psi> = 3/(4k^4)")
    print()

    print("ALL TESTS PASSED")
    return 0

if __name__ == "__main__":
    sys.exit(main())
