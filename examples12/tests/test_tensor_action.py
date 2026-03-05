#!/tmp/cas-venv/bin/python3
"""
Verify step 5.1.2: Tensor (TT) sector action.

For the transverse-traceless tensor h^{TT}_{ij}:
    R_{ij} = -(1/2) Box h^{TT}_{ij}
    R_{00} = R_{0i} = 0
    R = 0 (since h = 0 for traceless perturbation)

Therefore:
    R_{mu nu} R^{mu nu} = R_{ij} R^{ij} = (1/4)(Box h^{TT}_{ij})^2
    beta R^2 = 0

So I_{TT} = (1/4) int (Box h^{TT}_{ij})^2
         = (1/4) int h^{TT}_{ij} Box^2 h^{TT}_{ij}  (after IBP)

In Fourier space: (1/4) p^4 |h^{TT}_{ij}|^2
"""
import sys
from sympy import (symbols, Function, diff, simplify, expand,
                   Rational, Matrix, diag)

def main():
    print("=" * 60)
    print("TEST: Step 5.1.2 — Tensor (TT) sector action")
    print("=" * 60)
    print()

    t, x, y, z = symbols('t x y z')
    coords = [t, x, y, z]

    # We use two independent TT polarizations. For k along z:
    # h_+ : h_{xx} = -h_{yy} = h(t,z), h_{xy} = 0
    # h_x : h_{xy} = h_{yx} = h(t,z), h_{xx} = h_{yy} = 0
    #
    # Let's verify with h_+ polarization: h_{xx} = f, h_{yy} = -f, rest = 0
    # where f = f(t,z) (plane wave along z).

    f = Function('f')(t, z)

    # Build h_{mu nu} for plus polarization
    h = Matrix([
        [0, 0, 0, 0],
        [0, f, 0, 0],
        [0, 0, -f, 0],
        [0, 0, 0, 0]
    ])

    eta_inv = diag(-1, 1, 1, 1)

    # h^lambda_{  nu} = eta^{lambda alpha} h_{alpha nu}
    h_mixed = eta_inv * h

    # Trace h = eta^{mu nu} h_{mu nu} = h_{xx} + h_{yy} = f - f = 0
    trace_h = sum(eta_inv[mu, mu] * h[mu, mu] for mu in range(4))
    print(f"h (trace) = {trace_h}")
    assert trace_h == 0, "FAIL: trace should be 0 for TT mode"
    print("PASS: h = 0 (traceless)")
    print()

    # Box operator
    def box(g):
        return -diff(g, t, 2) + diff(g, z, 2)  # only t,z dependence for plane wave along z

    # Full box for general functions
    def box_full(g):
        return -diff(g, t, 2) + diff(g, x, 2) + diff(g, y, 2) + diff(g, z, 2)

    # Linearized Ricci tensor
    # 2 R_{mu nu} = d_lam d_mu h^lam_nu + d_lam d_nu h^lam_mu - Box h_{mu nu} - d_mu d_nu h
    # Since h = 0, the last term vanishes.

    def ricci_2(mu_idx, nu_idx):
        result = 0
        for lam in range(4):
            if h_mixed[lam, nu_idx] != 0:
                result += diff(diff(h_mixed[lam, nu_idx], coords[lam]), coords[mu_idx])
            if h_mixed[lam, mu_idx] != 0:
                result += diff(diff(h_mixed[lam, mu_idx], coords[lam]), coords[nu_idx])
        if h[mu_idx, nu_idx] != 0:
            result -= box_full(h[mu_idx, nu_idx])
        # d_mu d_nu h = 0 since h = 0
        return expand(result)

    # --- Verify R_{00} = 0 ---
    two_R00 = ricci_2(0, 0)
    print(f"2 R_00 = {two_R00}")
    assert two_R00 == 0, f"FAIL: R_00 should be 0, got {two_R00}"
    print("PASS: R_00 = 0")
    print()

    # --- Verify R_{0i} = 0 ---
    for i_idx, name in [(1, 'x'), (2, 'y'), (3, 'z')]:
        two_R0i = ricci_2(0, i_idx)
        print(f"2 R_0{name} = {two_R0i}")
        assert simplify(two_R0i) == 0, f"FAIL: R_0{name} should be 0, got {two_R0i}"
        print(f"PASS: R_0{name} = 0")
    print()

    # --- Verify R_{ij} = -(1/2) Box h^{TT}_{ij} ---
    print("--- Spatial Ricci components ---")
    for i_idx in range(1, 4):
        for j_idx in range(i_idx, 4):
            two_Rij = ricci_2(i_idx, j_idx)
            Rij = expand(Rational(1,2) * two_Rij)
            expected_Rij = expand(Rational(-1, 2) * box_full(h[i_idx, j_idx]))

            i_name = ['x', 'y', 'z'][i_idx - 1]
            j_name = ['x', 'y', 'z'][j_idx - 1]

            if h[i_idx, j_idx] != 0:
                diff_ij = simplify(Rij - expected_Rij)
                print(f"R_{{{i_name}{j_name}}} = {Rij}")
                print(f"-(1/2) Box h_{{{i_name}{j_name}}} = {expected_Rij}")
                print(f"Difference = {diff_ij}")
                assert diff_ij == 0, f"FAIL: R_{{{i_name}{j_name}}}"
                print(f"PASS: R_{{{i_name}{j_name}}} = -(1/2) Box h_{{{i_name}{j_name}}}")
            else:
                print(f"R_{{{i_name}{j_name}}} = {Rij} (h_{{{i_name}{j_name}}} = 0)")
                assert simplify(Rij) == 0, f"FAIL: R_{{{i_name}{j_name}}} should be 0"
                print(f"PASS: R_{{{i_name}{j_name}}} = 0")
    print()

    # --- Verify R = 0 ---
    R_scalar = 0
    for mu in range(4):
        two_Rmm = ricci_2(mu, mu)
        R_scalar += eta_inv[mu, mu] * Rational(1, 2) * two_Rmm
    R_scalar = expand(R_scalar)
    print(f"R = {R_scalar}")
    assert R_scalar == 0, f"FAIL: R should be 0, got {R_scalar}"
    print("PASS: R = 0 (traceless perturbation)")
    print()

    # --- Compute R_{mu nu} R^{mu nu} ---
    # = eta^{mu alpha} eta^{nu beta} R_{mu nu} R_{alpha beta}
    # = sum_{i,j} R_{ij} R_{ij}  (since R_{00} = R_{0i} = 0, and eta^{ii} = 1)
    RmnRmn = 0
    for i_idx in range(1, 4):
        for j_idx in range(1, 4):
            Rij = expand(Rational(1, 2) * ricci_2(i_idx, j_idx))
            RmnRmn += Rij**2
    RmnRmn = expand(RmnRmn)
    print(f"R_{{mu nu}} R^{{mu nu}} = {RmnRmn}")

    # Expected: (1/4)(Box f)^2 + (1/4)(Box(-f))^2 = (1/4)(Box f)^2 + (1/4)(Box f)^2
    #         = (1/2)(Box f)^2
    # For plus polarization with h_{xx} = f, h_{yy} = -f:
    # sum_{ij} (1/4)(Box h_{ij})^2 = (1/4)(Box f)^2 + (1/4)(Box f)^2 = (1/2)(Box f)^2
    box_f = box_full(f)
    expected_RR = Rational(1, 2) * box_f**2

    diff_RR = simplify(expand(RmnRmn - expected_RR))
    print(f"Expected (1/2)(Box f)^2 = {expand(expected_RR)}")
    print(f"Difference = {diff_RR}")
    assert diff_RR == 0, f"FAIL: R_munu R^munu mismatch"
    print("PASS: R_{mu nu} R^{mu nu} = (1/2)(Box f)^2 for plus polarization")
    print()

    # For a single TT component h_{ij}:
    # R_{ij} R^{ij} = (1/4)(Box h_{ij})^2 summed over i,j
    # For general TT: sum gives (1/4)(Box h^{TT}_{ij})^2 summed
    # The action I_{TT} = int R_{mu nu} R^{mu nu} - beta R^2
    #                    = (1/4) int (Box h^{TT}_{ij})^2
    print("--- Action for TT sector ---")
    print("I_{TT} = int [R_{mu nu} R^{mu nu} - beta R^2]")
    print("       = int R_{ij} R^{ij}  (since R_00 = R_0i = R = 0)")
    print("       = (1/4) int (Box h^{TT}_{ij})^2")
    print("       = (1/4) int h^{TT}_{ij} Box^2 h^{TT}_{ij}  (after IBP)")
    print()

    # --- Fourier space propagator ---
    print("--- Fourier-space propagator ---")
    k2, omega2, p4 = symbols('k2 omega2 p4', positive=True)
    # Box -> -p^2 in Fourier, so Box^2 -> p^4
    # Action = (1/4) p^4 |h^{TT}|^2
    # Propagator = 2/p^4  (factor 2 from the 1/2 in path integral, divided by 1/4)
    # Wait: action = (1/2) * (1/2) p^4 |h|^2 per polarization
    # Actually from the calculation above: for plus polarization,
    # R_{mu nu} R^{mu nu} = (1/2)(Box f)^2
    # In Fourier: (1/2) p^4 |f|^2
    # The propagator for f is: <f f> = 1/(p^4/2 * 2) ... let's be careful.
    # The Euclidean action is I = int (1/2) p^4 |f|^2  [for plus polarization alone]
    # So <f f> = 1/p^4  [since I = (1/2) * p^4 * |f|^2, propagator = 1/p^4]
    # Hmm, but the overall action normalization matters.
    # For the standard R_{mu nu}^2 + ... action (not 1/2 * that), we'd get:
    # <h^{TT}_{ij} h^{TT}_{kl}> = (TT projector) * 2/p^4

    print("For plus polarization: action integrand = (1/2) p^4 |f|^2")
    print("Propagator: <f f> = 1/p^4")
    print("General TT propagator: <h^TT_{ij} h^TT_{kl}> = Pi^{TT}_{ijkl} * 2/p^4")
    print()

    # --- Verify beta independence ---
    print("--- Beta independence of TT sector ---")
    beta = symbols('beta')
    # The action is R_{mu nu} R^{mu nu} - beta R^2
    # Since R = 0 for TT perturbations, the beta term vanishes identically.
    # This means the TT propagator is independent of beta.
    action_TT = expand(RmnRmn - beta * R_scalar**2)
    diff_beta = simplify(action_TT - RmnRmn)
    print(f"I_TT with beta term = {expand(action_TT)}")
    print(f"I_TT without beta term = {expand(RmnRmn)}")
    print(f"Difference = {diff_beta}")
    assert diff_beta == 0, "FAIL: beta term should vanish"
    print("PASS: TT sector is beta-independent (R=0 => beta R^2 = 0)")
    print()

    print("ALL TESTS PASSED")
    return 0

if __name__ == "__main__":
    sys.exit(main())
