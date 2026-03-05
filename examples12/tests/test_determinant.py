#!/tmp/cas-venv/bin/python3
"""
Verify Lemma 6.1: det(M) = 8(1 - 3*beta)*k^4*p^4

The kinetic matrix M for the scalar sector (Phi, psi) has entries:
    M_11 = 2(1 - 2*beta)*k^4
    M_12 = 4(1 - 3*beta)*k^2*p^2 + 2(1 - 2*beta)*k^4
    M_22 = 12(1 - 3*beta)*p^4 + 8(1 - 3*beta)*k^2*p^2 + 2(1 - 2*beta)*k^4

We verify M_11*M_22 - M_12^2 = 8(1 - 3*beta)*k^4*p^4.
"""
import sys
from sympy import symbols, expand, simplify, factor, Rational

def main():
    beta, k, p = symbols('beta k p')

    # Matrix entries
    M11 = 2 * (1 - 2*beta) * k**4
    M12 = 4 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4
    M22 = 12 * (1 - 3*beta) * p**4 + 8 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4

    # Determinant
    det_M = expand(M11 * M22 - M12**2)
    target = 8 * (1 - 3*beta) * k**4 * p**4

    diff = simplify(det_M - target)

    print("=" * 60)
    print("TEST: Lemma 6.1 — Determinant of scalar kinetic matrix")
    print("=" * 60)
    print()
    print(f"M_11 = {M11}")
    print(f"M_12 = {M12}")
    print(f"M_22 = {M22}")
    print()
    print(f"det(M) = M_11*M_22 - M_12^2")
    print(f"       = {det_M}")
    print()
    print(f"Target = {target}")
    print(f"       = {expand(target)}")
    print()
    print(f"Difference = {diff}")
    print()

    # Also verify the factored form
    det_factored = factor(det_M)
    print(f"det(M) factored = {det_factored}")
    print()

    assert diff == 0, f"FAIL: det(M) - target = {diff}"
    print("PASS: det(M) = 8(1 - 3*beta)*k^4*p^4")
    print()

    # Cross-check: expand both sides and compare
    assert expand(det_M) == expand(target), "FAIL: expanded forms differ"
    print("PASS: expanded forms match")
    print()

    # Verify specific numerical values
    # At beta=0: det = 8*k^4*p^4
    det_at_0 = det_M.subs(beta, 0)
    assert simplify(det_at_0 - 8*k**4*p**4) == 0, "FAIL at beta=0"
    print("PASS: beta=0 gives det = 8*k^4*p^4")

    # At beta=1/3: det = 0 (conformal gravity)
    det_at_third = det_M.subs(beta, Rational(1, 3))
    assert simplify(det_at_third) == 0, "FAIL at beta=1/3"
    print("PASS: beta=1/3 gives det = 0 (conformal gravity)")

    # At beta=1/2: det = -4*k^4*p^4
    det_at_half = det_M.subs(beta, Rational(1, 2))
    assert simplify(det_at_half - (-4*k**4*p**4)) == 0, "FAIL at beta=1/2"
    print("PASS: beta=1/2 gives det = -4*k^4*p^4")

    print()
    print("ALL TESTS PASSED")
    return 0

if __name__ == "__main__":
    sys.exit(main())
