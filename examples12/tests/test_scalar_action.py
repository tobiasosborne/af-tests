#!/tmp/cas-venv/bin/python3
"""
Verify the scalar sector matrix M derivation.

In the scalar gauge h_00 = 2*Phi, h_0i = 0, h_ij = 2*psi*delta_ij,
the quadratic action I = int [R_{mu nu} R^{mu nu} - beta R^2] can be
written in Fourier space as

    I_scalar = (Phi*, psi*) M (Phi, psi)

where M is a 2x2 Hermitian matrix (real-symmetric since coefficients are real).

Fourier conventions:
    nabla^2 f -> -k^2 f~
    f_ddot    -> -omega^2 f~
    Box f = (-d_t^2 + nabla^2) f -> (omega^2 - k^2) f~ = p^2 f~
    where p^2 = omega^2 - k^2.

Ricci components in Fourier space (from test_ricci_scalar_sector.py):
    R_00   = k^2 Phi + 3 omega^2 psi
    R_0i   -> sum_i |R_0i|^2 = 4 k^2 omega^2 |psi|^2
    R_ij   = -k_i k_j (Phi - psi) - p^2 psi delta_ij
    R      = -2 k^2 Phi + 4 k^2 psi - 6 omega^2 psi

Key IBP identity for the spatial contraction:
    sum_{ij} k_i k_j k_i k_j |Phi-psi|^2 = k^4 |Phi-psi|^2
(after integration by parts: d_i d_j f * d_i d_j f -> f nabla^4 f = (nabla^2 f)^2).

We verify that the matrix M has entries:
    M_11 = 2(1 - 2 beta) k^4
    M_12 = 4(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4
    M_22 = 12(1 - 3 beta) p^4 + 8(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4
"""
import sys
from sympy import (symbols, expand, simplify, collect, Rational, Poly,
                   Matrix, Symbol)


def main():
    print("=" * 60)
    print("TEST: Scalar sector matrix M derivation")
    print("=" * 60)
    print()

    k, omega, beta = symbols('k omega beta')
    p2 = omega**2 - k**2  # p^2 = omega^2 - k^2
    Phi, psi = symbols('Phi psi')

    # ================================================================
    # Part 1: Ricci components in Fourier space
    # ================================================================
    print("--- Part 1: Ricci components in Fourier space ---")
    print()

    # From the linearized Ricci tensor in scalar gauge:
    # R_00 = -nabla^2 Phi - 3 psi_ddot -> k^2 Phi + 3 omega^2 psi
    R00 = k**2 * Phi + 3 * omega**2 * psi
    print(f"R_00 = {R00}")

    # R_0i = -2 d_i psi_dot
    # In Fourier: R_0i -> -2 (i k_i)(- i omega) psi = -2 k_i omega psi
    # sum_i R_0i R_0i = 4 k^2 omega^2 |psi|^2  (using k_i k_i = k^2)
    # We track this as a scalar contribution to |psi|^2
    R0i_sq_sum = 4 * k**2 * omega**2  # coefficient of |psi|^2

    # R_ij = -k_i k_j (Phi - psi) - p^2 psi delta_ij (in Fourier)
    # R = -2 k^2 Phi + 4 k^2 psi - 6 omega^2 psi
    R_scalar = -2 * k**2 * Phi + 4 * k**2 * psi - 6 * omega**2 * psi
    R_scalar = expand(R_scalar)
    print(f"R = {R_scalar}")
    print()

    # ================================================================
    # Part 2: Compute R_{mu nu} R^{mu nu} with Lorentzian signature
    # ================================================================
    # R_{mu nu} R^{mu nu} = eta^{mu a} eta^{nu b} R_{mu nu} R_{ab}
    # With signature (-,+,+,+):
    #   = (R_00)^2 * (eta^00)^2 - 2 sum_i (R_0i)^2 * eta^00 eta^ii + sum_{ij} (R_ij)^2
    #   = (R_00)^2 - 2 sum_i (R_0i)^2 + sum_{ij} (R_ij)^2
    # (since eta^00 = -1 and eta^ii = +1)

    print("--- Part 2: R_{mu nu} R^{mu nu} ---")
    print()

    # Term 1: (R_00)^2
    term_R00_sq = expand(R00**2)
    print(f"(R_00)^2 = {term_R00_sq}")

    # Term 2: -2 sum_i R_0i R_0i
    # = -2 * 4 k^2 omega^2 |psi|^2 = -8 k^2 omega^2 |psi|^2
    term_R0i_sq = -2 * R0i_sq_sum * psi**2
    term_R0i_sq = expand(term_R0i_sq)
    print(f"-2 sum_i (R_0i)^2 = {term_R0i_sq}")

    # Term 3: sum_{ij} R_ij R_ij
    # R_ij = -k_i k_j (Phi - psi) - p^2 psi delta_ij
    #
    # R_ij R_ij = [k_i k_j (Phi-psi)]^2 + 2 [k_i k_j (Phi-psi)][p^2 psi delta_ij]
    #           + [p^2 psi]^2 delta_ij delta_ij
    #
    # First term: sum_{ij} k_i k_j k_i k_j (Phi-psi)^2
    #   After IBP: = k^4 (Phi-psi)^2
    #
    # Cross term: sum_{ij} 2 k_i k_j (Phi-psi) p^2 psi delta_ij
    #   = 2 p^2 psi (Phi-psi) sum_i k_i k_i = 2 k^2 p^2 psi (Phi-psi)
    #
    # Last term: sum_{ij} p^4 psi^2 delta_ij delta_ij
    #   = 3 p^4 psi^2  (since delta_ij delta_ij = delta_ii = 3)

    diff_Phi_psi = Phi - psi
    Rij_sq_term1 = k**4 * diff_Phi_psi**2
    Rij_sq_cross = 2 * k**2 * p2 * psi * diff_Phi_psi
    Rij_sq_term3 = 3 * p2**2 * psi**2

    term_Rij_sq = expand(Rij_sq_term1 + Rij_sq_cross + Rij_sq_term3)
    print(f"sum_{{ij}} (R_ij)^2 = {term_Rij_sq}")
    print()

    # Total R_{mu nu} R^{mu nu}
    RmnRmn = expand(term_R00_sq + term_R0i_sq + term_Rij_sq)
    print(f"R_{{mu nu}} R^{{mu nu}} = {RmnRmn}")
    print()

    # ================================================================
    # Part 3: Compute beta R^2
    # ================================================================
    print("--- Part 3: beta R^2 ---")
    print()

    R_sq = expand(R_scalar**2)
    beta_R_sq = expand(beta * R_sq)
    print(f"R^2 = {R_sq}")
    print()

    # ================================================================
    # Part 4: Full action integrand and extract matrix M
    # ================================================================
    # I = R_{mu nu} R^{mu nu} - beta R^2

    print("--- Part 4: Action integrand and matrix M ---")
    print()

    action = expand(RmnRmn - beta_R_sq)
    print(f"I = R_munu R^munu - beta R^2 = {action}")
    print()

    # Collect in terms of |Phi|^2, Phi*psi (=Re(Phi*psi) symmetric part), |psi|^2
    # The action is a quadratic form: I = M_11 |Phi|^2 + 2 M_12 Re(Phi* psi) + M_22 |psi|^2
    # where the factor 2 in front of M_12 is the standard convention for symmetric bilinear form.
    # In terms of real symbols: I = M_11 Phi^2 + 2 M_12 Phi psi + M_22 psi^2.

    # Extract coefficients
    action_poly = Poly(action, Phi, psi)

    M11_computed = action_poly.nth(2, 0)  # coefficient of Phi^2
    M12_times_2 = action_poly.nth(1, 1)   # coefficient of Phi*psi (this is 2*M_12)
    M22_computed = action_poly.nth(0, 2)   # coefficient of psi^2

    M11 = expand(M11_computed)
    M12 = expand(M12_times_2 / 2)
    M22 = expand(M22_computed)

    print(f"M_11 (coefficient of |Phi|^2)     = {M11}")
    print(f"M_12 (half coeff of Phi*psi)      = {M12}")
    print(f"M_22 (coefficient of |psi|^2)     = {M22}")
    print()

    # ================================================================
    # Part 5: Rewrite in terms of p^2 = omega^2 - k^2 and verify
    # ================================================================
    print("--- Part 5: Rewrite in terms of p^2 and verify ---")
    print()

    # Substitute omega^2 = p2_sym + k^2
    p2_sym = Symbol('p2')

    def to_p2(expr):
        """Replace omega^2 -> p2_sym + k^2 and simplify."""
        return expand(expr.subs(omega**2, p2_sym + k**2))

    M11_p = to_p2(M11)
    M12_p = to_p2(M12)
    M22_p = to_p2(M22)

    print(f"M_11 in terms of p^2: {M11_p}")
    print(f"M_12 in terms of p^2: {M12_p}")
    print(f"M_22 in terms of p^2: {M22_p}")
    print()

    # Expected values:
    # M_11 = 2(1 - 2 beta) k^4
    M11_expected = 2 * (1 - 2*beta) * k**4

    # M_12 = 4(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4
    M12_expected = 4 * (1 - 3*beta) * k**2 * p2_sym + 2 * (1 - 2*beta) * k**4

    # M_22 = 12(1 - 3 beta) p^4 + 8(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4
    M22_expected = (12 * (1 - 3*beta) * p2_sym**2
                    + 8 * (1 - 3*beta) * k**2 * p2_sym
                    + 2 * (1 - 2*beta) * k**4)

    # Verify M_11
    diff_M11 = simplify(expand(M11_p - M11_expected))
    print(f"M_11 expected: {expand(M11_expected)}")
    print(f"M_11 - expected = {diff_M11}")
    assert diff_M11 == 0, f"FAIL: M_11 mismatch, diff = {diff_M11}"
    print("PASS: M_11 = 2(1 - 2 beta) k^4")
    print()

    # Verify M_12
    diff_M12 = simplify(expand(M12_p - M12_expected))
    print(f"M_12 expected: {expand(M12_expected)}")
    print(f"M_12 - expected = {diff_M12}")
    assert diff_M12 == 0, f"FAIL: M_12 mismatch, diff = {diff_M12}"
    print("PASS: M_12 = 4(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4")
    print()

    # Verify M_22
    diff_M22 = simplify(expand(M22_p - M22_expected))
    print(f"M_22 expected: {expand(M22_expected)}")
    print(f"M_22 - expected = {diff_M22}")
    assert diff_M22 == 0, f"FAIL: M_22 mismatch, diff = {diff_M22}"
    print("PASS: M_22 = 12(1 - 3 beta) p^4 + 8(1 - 3 beta) k^2 p^2 + 2(1 - 2 beta) k^4")
    print()

    # ================================================================
    # Part 6: Cross-checks
    # ================================================================
    print("--- Part 6: Cross-checks ---")
    print()

    # Cross-check 1: At beta = 1/3 (Weyl-squared action), the (1-3beta) terms vanish
    # M_11(1/3) = 2(1 - 2/3) k^4 = (2/3) k^4
    # M_12(1/3) = 0 + 2(1/3) k^4 = (2/3) k^4
    # M_22(1/3) = 0 + 0 + (2/3) k^4
    M11_weyl = expand(M11_p.subs(beta, Rational(1, 3)))
    M12_weyl = expand(M12_p.subs(beta, Rational(1, 3)))
    M22_weyl = expand(M22_p.subs(beta, Rational(1, 3)))

    assert simplify(M11_weyl - Rational(2, 3) * k**4) == 0, \
        f"FAIL: M_11(1/3) should be (2/3)k^4, got {M11_weyl}"
    assert simplify(M12_weyl - Rational(2, 3) * k**4) == 0, \
        f"FAIL: M_12(1/3) should be (2/3)k^4, got {M12_weyl}"
    assert simplify(M22_weyl - Rational(2, 3) * k**4) == 0, \
        f"FAIL: M_22(1/3) should be (2/3)k^4, got {M22_weyl}"
    print("PASS: At beta=1/3 (Weyl^2), M = (2/3) k^4 * [[1,1],[1,1]]")
    print(f"  M_11 = {M11_weyl}, M_12 = {M12_weyl}, M_22 = {M22_weyl}")

    # This means the Weyl action for scalars is (2/3) k^4 (Phi + psi)^2,
    # which is rank 1 (as expected: Weyl is conformally invariant, one combination is pure gauge).
    M_weyl = Matrix([[M11_weyl, M12_weyl], [M12_weyl, M22_weyl]])
    det_weyl = expand(M_weyl.det())
    print(f"  det(M_weyl) = {det_weyl}")
    assert det_weyl == 0, f"FAIL: Weyl matrix should have rank 1, det = {det_weyl}"
    print("PASS: M_weyl has rank 1 (conformal mode decouples)")
    print()

    # Cross-check 2: At beta = 1/2, the (1-2beta) terms vanish
    M11_half = expand(M11_p.subs(beta, Rational(1, 2)))
    M12_half = expand(M12_p.subs(beta, Rational(1, 2)))
    M22_half = expand(M22_p.subs(beta, Rational(1, 2)))
    assert M11_half == 0, f"FAIL: M_11(1/2) should be 0, got {M11_half}"
    print("PASS: At beta=1/2, M_11 = 0 (R^2 term kills Phi^2 coefficient)")
    print(f"  M_11 = {M11_half}, M_12 = {M12_half}, M_22 = {M22_half}")
    print()

    # Cross-check 3: At beta = 0 (pure R_{mu nu}^2 action)
    M11_0 = expand(M11_p.subs(beta, 0))
    M12_0 = expand(M12_p.subs(beta, 0))
    M22_0 = expand(M22_p.subs(beta, 0))
    assert simplify(M11_0 - 2*k**4) == 0
    assert simplify(M12_0 - (4*k**2*p2_sym + 2*k**4)) == 0
    assert simplify(M22_0 - (12*p2_sym**2 + 8*k**2*p2_sym + 2*k**4)) == 0
    print("PASS: At beta=0, M entries match pure R_{mu nu}^2 action")
    print(f"  M_11 = {M11_0}")
    print(f"  M_12 = {M12_0}")
    print(f"  M_22 = {M22_0}")
    print()

    # Cross-check 4: On-shell (p^2 = 0) simplification
    M11_on = M11_p.subs(p2_sym, 0)
    M12_on = M12_p.subs(p2_sym, 0)
    M22_on = M22_p.subs(p2_sym, 0)
    print(f"On-shell (p^2=0): M_11={M11_on}, M_12={M12_on}, M_22={M22_on}")
    # All should be 2(1-2beta) k^4
    assert simplify(M11_on - M12_on) == 0 and simplify(M12_on - M22_on) == 0, \
        "FAIL: On-shell matrix should be proportional to [[1,1],[1,1]]"
    print("PASS: On-shell, M = 2(1-2beta) k^4 * [[1,1],[1,1]] (rank 1)")
    print()

    print("ALL TESTS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
