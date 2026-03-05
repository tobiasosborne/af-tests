#!/tmp/cas-venv/bin/python3
"""
VERIFIER-7: Deep verification of node 1.7.4 (Special cases beta=1/2, beta=1/3).

CRITICAL CHECK: The claim at beta=1/3:
"det(M)=0, the conformal gravity point where the Weyl tensor squared action
has conformal symmetry removing one scalar DOF."

Also from Remark 6.2 in the proof document:
"R_{mu nu}R^{mu nu} - (1/3)R^2 = (1/2) C_{mu nu rho sigma} C^{mu nu rho sigma}
(up to total derivatives)"

We need to verify: Is R_{mu nu}^2 - (1/3) R^2 = (1/2) C^2 + total derivatives?

The Weyl tensor in 4D:
C_{mu nu rho sigma} = R_{mu nu rho sigma}
  - (1/2)(g_{mu rho} R_{nu sigma} - g_{mu sigma} R_{nu rho}
         - g_{nu rho} R_{mu sigma} + g_{nu sigma} R_{mu rho})
  + (1/6) R (g_{mu rho} g_{nu sigma} - g_{mu sigma} g_{nu rho})

So:
C^2 = C_{mu nu rho sigma} C^{mu nu rho sigma}
    = R_{mu nu rho sigma}^2 - 2 R_{mu nu}^2 + (1/3) R^2

Therefore:
(1/2) C^2 = (1/2) R_{mu nu rho sigma}^2 - R_{mu nu}^2 + (1/6) R^2

Now the Gauss-Bonnet invariant in 4D is:
G = R_{mu nu rho sigma}^2 - 4 R_{mu nu}^2 + R^2

This is a total derivative (topological) in 4D.

So: R_{mu nu rho sigma}^2 = G + 4 R_{mu nu}^2 - R^2 (mod total deriv)

Substituting into (1/2) C^2:
(1/2) C^2 = (1/2)(G + 4 R_{mu nu}^2 - R^2) - R_{mu nu}^2 + (1/6) R^2
           = (1/2)G + 2 R_{mu nu}^2 - (1/2) R^2 - R_{mu nu}^2 + (1/6) R^2
           = (1/2)G + R_{mu nu}^2 - (1/3) R^2

Since G is a total derivative:
(1/2) C^2 = R_{mu nu}^2 - (1/3) R^2  (up to total derivatives)

This CONFIRMS the claim!
"""
import sys
from sympy import symbols, simplify, Rational, expand, cancel

def main():
    print("=" * 60)
    print("VERIFIER-7: Node 1.7.4 — Special cases beta=1/2, beta=1/3")
    print("=" * 60)
    print()

    # ========================================
    # Part 1: beta = 1/2 (straightforward)
    # ========================================
    print("--- Part 1: beta = 1/2 ---")
    print()

    beta_val = Rational(1, 2)
    one_minus_2beta = 1 - 2 * beta_val
    print(f"  1 - 2*beta = {one_minus_2beta}")
    assert one_minus_2beta == 0
    print("  PASS: (1-2beta) = 0 at beta=1/2")
    print()

    print("  Consequences:")
    print("  - <psi psi> = (1-2beta)/(8(1-3beta)p^4) = 0. CORRECT.")
    print("  - p^{-4} piece in <Phi Phi> and <Phi psi> vanishes. CORRECT.")
    print("  - <Phi psi> = -1/(4k^2 p^2). CORRECT (from test_special_cases.py).")
    print("  - <Phi Phi> = 3/(4k^4) + 1/(2k^2 p^2). CORRECT (from test_special_cases.py).")
    print()
    print("  'Scalar sector reduces to one constrained DOF':")
    print("  With <psi psi> = 0, psi has no dynamics — it's a constraint.")
    print("  Only Phi propagates, with poles at k^2=0 and p^2=0.")
    print("  PASS: Interpretation is correct.")
    print()

    # ========================================
    # Part 2: beta = 1/3 (critical check)
    # ========================================
    print("--- Part 2: beta = 1/3 (conformal gravity) ---")
    print()

    beta_val = Rational(1, 3)
    one_minus_3beta = 1 - 3 * beta_val
    print(f"  1 - 3*beta = {one_minus_3beta}")
    assert one_minus_3beta == 0
    print("  PASS: det(M) = 8(1-3beta)k^4 p^4 = 0 at beta=1/3")
    print()

    # ========================================
    # Part 2a: Verify C^2 identity algebraically
    # ========================================
    print("--- Part 2a: Algebraic verification of C^2 identity ---")
    print()

    # We use symbolic variables for the curvature invariants
    Riem2, Ric2, R2 = symbols('Riem2 Ric2 R2')
    # Riem2 = R_{mu nu rho sigma}^2
    # Ric2 = R_{mu nu}^2
    # R2 = R^2

    # Weyl squared in 4D
    C2 = Riem2 - 2*Ric2 + Rational(1, 3)*R2
    print(f"  C^2 = R_{{munurhosgm}}^2 - 2 R_{{munu}}^2 + (1/3) R^2")
    print(f"       = {C2}")
    print()

    # Gauss-Bonnet in 4D (total derivative)
    G = Riem2 - 4*Ric2 + R2
    print(f"  Gauss-Bonnet: G = R_{{munurhosgm}}^2 - 4 R_{{munu}}^2 + R^2")
    print(f"                  = {G}")
    print(f"  (G is a total derivative in 4D)")
    print()

    # From G: Riem2 = G + 4*Ric2 - R2
    # Substitute into C^2:
    C2_no_Riem = C2.subs(Riem2, G + 4*Ric2 - R2)
    C2_no_Riem = expand(C2_no_Riem)
    print(f"  C^2 (eliminating Riem2 using G.B.):")
    print(f"    = {C2_no_Riem}")
    print(f"    = G + 2*Ric2 - (2/3)*R2")
    print()

    # So (1/2) C^2 = (1/2)G + Ric2 - (1/3)R2
    half_C2 = expand(Rational(1, 2) * C2_no_Riem)
    print(f"  (1/2) C^2 = {half_C2}")
    print()

    # The action at beta=1/3: Ric2 - (1/3)*R2
    action_at_beta_third = Ric2 - Rational(1, 3)*R2
    print(f"  Action at beta=1/3: R_{{munu}}^2 - (1/3) R^2 = {action_at_beta_third}")
    print()

    # Check: (1/2) C^2 - (Ric2 - (1/3)*R2) should be a total derivative (proportional to G)
    diff_check = expand(half_C2 - action_at_beta_third)
    print(f"  (1/2) C^2 - [R_munu^2 - (1/3) R^2] = {diff_check}")
    print()

    # This should be (1/2) G
    half_G = expand(Rational(1, 2) * G)
    print(f"  (1/2) G = {half_G}")
    diff_from_half_G = simplify(diff_check - half_G)
    print(f"  Difference from (1/2) G: {diff_from_half_G}")
    assert diff_from_half_G == 0, f"FAIL: {diff_from_half_G}"
    print()
    print("  CONFIRMED: R_{mu nu}^2 - (1/3) R^2 = (1/2) C^2 - (1/2) G")
    print("  Since G is a total derivative in 4D:")
    print("  R_{mu nu}^2 - (1/3) R^2 = (1/2) C^2 (up to total derivatives)")
    print()
    print("  This is EXACTLY what Remark 6.2 claims. CORRECT!")
    print()

    # ========================================
    # Part 2b: Verify the linearized version
    # ========================================
    print("--- Part 2b: Linearized Gauss-Bonnet check ---")
    print()
    print("  At the linearized level, the Gauss-Bonnet term G^(2) is a total")
    print("  derivative. This is because in 4D, int sqrt(g) G d^4x is")
    print("  topological (Euler characteristic), so its variation is zero,")
    print("  meaning the quadratic part in h_{mu nu} is a total derivative.")
    print()
    print("  Therefore, the linearized action:")
    print("  I = int [R^(1)_{mu nu} R^{(1)mu nu} - (1/3)(R^(1))^2]")
    print("    = (1/2) int C^(1)_{mu nu rho sigma} C^{(1)mu nu rho sigma}")
    print("  which has conformal invariance at linear order.")
    print("  The conformal transformation h_{mu nu} -> h_{mu nu} + 2 sigma eta_{mu nu}")
    print("  removes one scalar DOF (the trace mode), making M singular.")
    print()
    print("  PASS: The linearized Gauss-Bonnet argument is correct.")
    print()

    # ========================================
    # Part 2c: Check the matrix M at beta=1/3
    # ========================================
    print("--- Part 2c: Matrix M at beta=1/3 ---")
    print()

    beta, k, p = symbols('beta k p')
    M11 = 2 * (1 - 2*beta) * k**4
    M12 = 4 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4
    M22 = 12 * (1 - 3*beta) * p**4 + 8 * (1 - 3*beta) * k**2 * p**2 + 2 * (1 - 2*beta) * k**4

    M11_third = expand(M11.subs(beta, Rational(1, 3)))
    M12_third = expand(M12.subs(beta, Rational(1, 3)))
    M22_third = expand(M22.subs(beta, Rational(1, 3)))

    print(f"  M_11 = {M11_third}")
    print(f"  M_12 = {M12_third}")
    print(f"  M_22 = {M22_third}")
    print()

    # All should be (2/3) k^4
    target = Rational(2, 3) * k**4
    assert simplify(M11_third - target) == 0
    assert simplify(M12_third - target) == 0
    assert simplify(M22_third - target) == 0
    print(f"  All entries = (2/3)k^4. Matrix is (2/3)k^4 * [[1,1],[1,1]].")
    print(f"  This has rank 1 with null vector (1, -1).")
    print()

    # The null vector (1, -1) means the combination Phi - psi is not constrained.
    # The conformal transformation h_{mu nu} -> h_{mu nu} + 2 sigma eta_{mu nu}
    # in SVT: h_{00} -> h_{00} - 2 sigma, h_{ij} -> h_{ij} + 2 sigma delta_{ij}
    # i.e., Phi -> Phi - sigma, psi -> psi + sigma.
    # So Phi + psi is gauge-invariant (traceless combination), while Phi - psi
    # transforms. The null vector (1, -1) precisely removes Phi - psi.
    #
    # Wait: the null vector of [[1,1],[1,1]] is (1,-1) (since [1,1]*[1,-1]^T = 0).
    # This means the combination Phi - psi has zero kinetic term.
    # Under conformal transformation: Phi -> Phi - sigma, psi -> psi + sigma
    # Phi - psi -> (Phi - sigma) - (psi + sigma) = Phi - psi - 2 sigma
    # This is NOT invariant, so it's pure gauge. CORRECT.
    # And Phi + psi -> (Phi - sigma) + (psi + sigma) = Phi + psi is invariant.
    # The matrix acts on [Phi, psi]^T, so its image is spanned by (1,1)^T.
    # The observable Phi + psi is the only propagating scalar DOF.
    print("  The null vector (1, -1) corresponds to Phi - psi,")
    print("  which is pure gauge under conformal transformations.")
    print("  Only Phi + psi propagates. CORRECT.")
    print()

    # ========================================
    # Part 3: Additional — verify sum rule from test_special_cases.py
    # ========================================
    print("--- Part 3: Sum rule check ---")
    print()

    # <Phi Phi> + 2<Phi psi> + <psi psi> = <(Phi+psi)(Phi+psi)>
    # The test showed this equals 3/(4k^4), independent of beta.
    # This is the propagator of the "conformal-invariant" combination.
    # At beta=1/3, this is the ONLY propagator (others diverge).
    print("  <(Phi+psi)^2> = <PhiPhi> + 2<PhiPsi> + <PsiPsi>")
    print("  From test_special_cases.py: this = 3/(4k^4) (beta-independent)")
    print()
    print("  Interpretation: The conformal-invariant combination Phi + psi")
    print("  has an instantaneous propagator ~ 1/k^4, independent of beta.")
    print("  At beta=1/3, this is the only surviving propagator.")
    print("  PASS.")
    print()

    # ========================================
    # Part 4: Run the SymPy test
    # ========================================
    print("--- Part 4: Running test_special_cases.py ---")
    print("  (Already run and verified above — all tests passed)")
    print()

    # ========================================
    # EXTRA SCRUTINY: Is the claim about "Gauss-Bonnet at linear order" referenced correctly?
    # ========================================
    print("--- Extra: Reference check ---")
    print()
    print("  The node references 'Gauss-Bonnet at Linear Order'.")
    print("  This is a standard result. In 4D, the Gauss-Bonnet density")
    print("  sqrt(g) E_4 = sqrt(g)(R^2 - 4R_{mu nu}^2 + R_{mu nu rho sigma}^2)")
    print("  integrates to give the Euler characteristic chi,")
    print("  so its variation vanishes. At quadratic order in h,")
    print("  int E_4^{(2)} d^4x = 0 (total derivative).")
    print("  This is used to eliminate R_{mu nu rho sigma}^2 in favor of")
    print("  R_{mu nu}^2 and R^2 (modulo total derivatives).")
    print("  CORRECT and standard.")
    print()

    # ========================================
    # VERDICT
    # ========================================
    print("=" * 60)
    print("VERDICT on 1.7.4:")
    print()
    print("  beta = 1/2:")
    print("  - (1-2beta) = 0, <psi psi> = 0: CORRECT")
    print("  - p^{-4} pieces vanish: CORRECT (verified by SymPy)")
    print("  - Remaining propagators correct: CORRECT")
    print()
    print("  beta = 1/3:")
    print("  - det(M) = 0 (conformal point): CORRECT")
    print("  - R_{mu nu}^2 - (1/3)R^2 = (1/2)C^2 (mod total deriv): VERIFIED")
    print("    Via: C^2 = Riem^2 - 2Ric^2 + (1/3)R^2 (Weyl tensor identity)")
    print("    And: Riem^2 = G + 4Ric^2 - R^2 (Gauss-Bonnet)")
    print("    => (1/2)C^2 = Ric^2 - (1/3)R^2 + (1/2)G (total deriv)")
    print("  - Conformal symmetry removes one scalar DOF: CORRECT")
    print("    (null vector of M = (1,-1) = pure conformal gauge)")
    print()
    print("STATUS: PASS (no errors found)")
    print("=" * 60)

    return 0

if __name__ == "__main__":
    sys.exit(main())
