#!/tmp/cas-venv/bin/python3
"""
VERIFIER-7: Independent algebraic check of the Weyl-squared identity.

The mission brief suggested checking:
"R_{mu nu}^2 - (1/3)R^2 = (1/2)C^2 up to total derivatives"

and raised a concern:
"(1/2)C^2 = (1/2)R_{munurhosigma}^2 - R_{mu nu}^2 + (1/6)R^2.
This gives R_{mu nu}^2 - (1/3)R^2 = (1/2)R_{munurhosigma}^2 - (1/2)C^2.
That doesn't simplify nicely."

Let's verify VERY carefully that it DOES simplify correctly when the
Gauss-Bonnet identity is used.
"""
import sys
from sympy import symbols, Rational, expand, simplify

def main():
    print("=" * 60)
    print("INDEPENDENT CHECK: Weyl-squared identity")
    print("=" * 60)
    print()

    # In 4 dimensions, the relevant quadratic curvature invariants are:
    # Riem2 = R_{mu nu rho sigma} R^{mu nu rho sigma}  (Kretschner scalar)
    # Ric2  = R_{mu nu} R^{mu nu}
    # R2    = R^2
    # C2    = C_{mu nu rho sigma} C^{mu nu rho sigma}  (Weyl squared)
    # G     = Gauss-Bonnet = Riem2 - 4*Ric2 + R2 (total derivative in 4D)

    # Standard 4D identity for Weyl:
    # C2 = Riem2 - 2*Ric2 + (1/3)*R2
    # (This comes from the definition of the Weyl tensor in D dimensions:
    #  C_{mu nu rho sigma} = R_{mu nu rho sigma}
    #    - (2/(D-2))(g_{mu[rho} R_{sigma]nu} - g_{nu[rho} R_{sigma]mu})
    #    + (2/((D-1)(D-2))) R g_{mu[rho} g_{sigma]nu}
    #  Squaring in D=4 gives C2 = Riem2 - 2Ric2 + (1/3)R2.)

    Riem2, Ric2, R2 = symbols('Riem2 Ric2 R2')

    C2 = Riem2 - 2*Ric2 + Rational(1, 3)*R2
    G = Riem2 - 4*Ric2 + R2

    print("Known identities:")
    print(f"  C^2 = {C2}")
    print(f"  G   = {G}  (total derivative in 4D)")
    print()

    # What we want to show:
    # Ric2 - (1/3)*R2 = (1/2)*C2  (mod total derivatives, i.e., mod G)
    #
    # Equivalently: Ric2 - (1/3)*R2 - (1/2)*C2 = c * G for some constant c.

    LHS = Ric2 - Rational(1, 3)*R2
    RHS_up_to_tdiv = Rational(1, 2)*C2

    difference = expand(LHS - RHS_up_to_tdiv)
    print(f"  LHS = Ric2 - (1/3) R2")
    print(f"  (1/2) C2 = {expand(RHS_up_to_tdiv)}")
    print(f"  LHS - (1/2) C2 = {difference}")
    print()

    # Express difference in terms of G:
    # LHS - (1/2)C2 = Ric2 - (1/3)R2 - (1/2)(Riem2 - 2Ric2 + (1/3)R2)
    #               = Ric2 - (1/3)R2 - (1/2)Riem2 + Ric2 - (1/6)R2
    #               = 2 Ric2 - (1/2) R2 - (1/2) Riem2
    #               = -(1/2)(Riem2 - 4 Ric2 + R2)
    #               = -(1/2) G

    should_be_neg_half_G = expand(difference + Rational(1, 2)*G)
    print(f"  LHS - (1/2) C2 + (1/2) G = {should_be_neg_half_G}")
    assert should_be_neg_half_G == 0, f"FAIL: got {should_be_neg_half_G}"
    print("  CONFIRMED: LHS - (1/2)C2 = -(1/2)G")
    print()
    print("  Therefore: Ric2 - (1/3)R2 = (1/2)C2 - (1/2)G")
    print("  Since G is a total derivative in 4D:")
    print("  Ric2 - (1/3)R2 = (1/2)C2 (up to total derivatives)")
    print()

    # Now let's address the concern from the mission brief:
    print("=" * 60)
    print("Addressing the mission brief concern:")
    print()
    print("The brief said:")
    print("  '(1/2)C^2 = (1/2)R_{munurhosigma}^2 - R_{munu}^2 + (1/6)R^2'")
    print("  'This gives R_{munu}^2 - (1/3)R^2 = (1/2)R_{munurhosigma}^2 - (1/2)C^2'")
    print("  'That doesn't simplify nicely.'")
    print()
    print("Let me verify:")
    brief_RHS = Rational(1, 2)*Riem2 - Rational(1, 2)*C2
    brief_RHS_expanded = expand(brief_RHS)
    print(f"  (1/2)Riem2 - (1/2)C2 = {brief_RHS_expanded}")

    # = (1/2)Riem2 - (1/2)(Riem2 - 2Ric2 + (1/3)R2)
    # = (1/2)Riem2 - (1/2)Riem2 + Ric2 - (1/6)R2
    # = Ric2 - (1/6)R2

    target = Ric2 - Rational(1, 6)*R2
    diff_check = simplify(brief_RHS_expanded - target)
    print(f"  This equals Ric2 - (1/6)R2: diff = {diff_check}")
    assert diff_check == 0
    print()
    print("  BUT we need Ric2 - (1/3)R2, not Ric2 - (1/6)R2!")
    print("  The brief's approach of writing Ric2 - (1/3)R2 = (1/2)Riem2 - (1/2)C2")
    print("  is WRONG because (1/2)Riem2 - (1/2)C2 = Ric2 - (1/6)R2, not Ric2 - (1/3)R2.")
    print()
    print("  The CORRECT approach requires eliminating Riem2 using Gauss-Bonnet:")
    print("  Riem2 = G + 4Ric2 - R2 (mod total derivatives)")
    print("  Then: (1/2)C2 = (1/2)(G + 4Ric2 - R2) - Ric2 + (1/6)R2")
    print("                = (1/2)G + Ric2 - (1/3)R2")
    print("  So: Ric2 - (1/3)R2 = (1/2)C2 - (1/2)G = (1/2)C2 (mod total deriv)")
    print()
    print("  The brief's concern was based on NOT using the Gauss-Bonnet identity.")
    print("  Once G-B is applied, the identity holds perfectly.")
    print()
    print("  CONCLUSION: The proof document's claim is CORRECT.")
    print("  The brief's confusion arose from trying to relate Ric2-(1/3)R2 to C2")
    print("  without eliminating Riem2, which is impossible without G-B.")
    print("=" * 60)

    return 0

if __name__ == "__main__":
    sys.exit(main())
