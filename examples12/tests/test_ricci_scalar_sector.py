#!/tmp/cas-venv/bin/python3
"""
Verify Claim 3.1 computationally.

In the scalar gauge h_00 = 2*Phi, h_0i = 0, h_ij = 2*psi*delta_ij,
we compute linearized Ricci tensor components and the Ricci scalar.

Linearized Ricci tensor (indices lowered with flat metric eta):
    2 R_{mu nu} = partial_lambda partial_mu h^lambda_nu
                + partial_lambda partial_nu h^lambda_mu
                - Box h_{mu nu}
                - partial_mu partial_nu h

where h = eta^{mu nu} h_{mu nu} is the trace, and Box = -partial_t^2 + nabla^2.

We verify:
    R_00 = -nabla^2 Phi - 3 ddot{psi}
    R_0i = -2 partial_i dot{psi}
    R = 2 nabla^2 Phi - 4 nabla^2 psi + 6 ddot{psi}
"""
import sys
from sympy import (symbols, Function, diff, simplify, expand,
                   Matrix, diag, eye, Rational)

def main():
    t, x, y, z = symbols('t x y z')
    coords = [t, x, y, z]

    # Scalar functions
    Phi = Function('Phi')(t, x, y, z)
    psi = Function('psi')(t, x, y, z)

    print("=" * 60)
    print("TEST: Claim 3.1 — Ricci tensor in scalar gauge")
    print("=" * 60)
    print()

    # Metric perturbation h_{mu nu} (lower indices)
    # h_00 = 2*Phi, h_0i = 0, h_ij = 2*psi*delta_ij
    # With signature (-,+,+,+): eta = diag(-1,1,1,1)
    # h^{00} = eta^{00} eta^{00} h_{00} = (-1)(-1)(2Phi) = 2Phi  ... wait
    # Actually h^{mu nu} = eta^{mu alpha} eta^{nu beta} h_{alpha beta}
    # h^{00} = eta^{00}*eta^{00}*h_{00} = 1 * 2Phi = 2Phi  (since eta^{00} = -1, squared = 1)
    # h^{0i} = 0
    # h^{ij} = delta^{ij} * 2*psi (since eta^{ij} = delta^{ij})

    # Build h_{mu nu} as a 4x4 matrix
    h = Matrix([
        [2*Phi, 0,     0,     0    ],
        [0,     2*psi, 0,     0    ],
        [0,     0,     2*psi, 0    ],
        [0,     0,     0,     2*psi]
    ])

    # Flat metric eta_{mu nu} = diag(-1,1,1,1)
    eta = diag(-1, 1, 1, 1)
    eta_inv = diag(-1, 1, 1, 1)  # eta^{mu nu}

    # Raise indices: h^{mu nu} = eta^{mu alpha} eta^{nu beta} h_{alpha beta}
    h_up = eta_inv * h * eta_inv

    # Trace: h = eta^{mu nu} h_{mu nu}
    trace_h = sum(eta_inv[mu, mu] * h[mu, mu] for mu in range(4))
    trace_h_simplified = expand(trace_h)
    print(f"h = eta^{{mu nu}} h_{{mu nu}} = {trace_h_simplified}")
    expected_trace = -2*Phi + 6*psi
    assert simplify(trace_h_simplified - expected_trace) == 0, \
        f"FAIL: trace should be -2*Phi + 6*psi, got {trace_h_simplified}"
    print(f"PASS: h = -2*Phi + 6*psi")
    print()

    # Box = eta^{mu nu} partial_mu partial_nu = -d_t^2 + d_x^2 + d_y^2 + d_z^2
    def box(f):
        return -diff(f, t, 2) + diff(f, x, 2) + diff(f, y, 2) + diff(f, z, 2)

    def laplacian(f):
        return diff(f, x, 2) + diff(f, y, 2) + diff(f, z, 2)

    # Linearized Ricci tensor:
    # 2 R_{mu nu} = d_lam d_mu h^lam_nu + d_lam d_nu h^lam_mu - Box h_{mu nu} - d_mu d_nu h
    # where h^lam_nu = eta^{lam alpha} h_{alpha nu}
    # Actually h^lambda_{  nu} = eta^{lambda alpha} h_{alpha nu}
    h_mixed = eta_inv * h  # h^lambda_{  nu} = eta^{lambda alpha} h_{alpha nu}

    def ricci_2(mu_idx, nu_idx):
        """Compute 2*R_{mu nu} using the linearized formula."""
        result = 0
        # Term 1: d_lambda d_mu h^lambda_nu
        for lam in range(4):
            result += diff(diff(h_mixed[lam, nu_idx], coords[lam]), coords[mu_idx])
        # Term 2: d_lambda d_nu h^lambda_mu
        for lam in range(4):
            result += diff(diff(h_mixed[lam, mu_idx], coords[lam]), coords[nu_idx])
        # Term 3: -Box h_{mu nu}
        result -= box(h[mu_idx, nu_idx])
        # Term 4: -d_mu d_nu h
        result -= diff(diff(trace_h, coords[mu_idx]), coords[nu_idx])
        return expand(result)

    # --- R_00 ---
    two_R00 = ricci_2(0, 0)
    R00 = expand(two_R00 / 2)
    print(f"2*R_00 = {two_R00}")
    print(f"R_00   = {R00}")

    R00_target = -laplacian(Phi) - 3*diff(psi, t, 2)
    diff_R00 = simplify(R00 - R00_target)
    print(f"Target R_00 = -nabla^2 Phi - 3 ddot(psi)")
    print(f"Difference  = {diff_R00}")
    assert diff_R00 == 0, f"FAIL: R_00 mismatch, diff = {diff_R00}"
    print("PASS: R_00 = -nabla^2 Phi - 3 ddot(psi)")
    print()

    # --- R_0i (check R_01 as representative) ---
    for i_idx, i_name in [(1, 'x'), (2, 'y'), (3, 'z')]:
        two_R0i = ricci_2(0, i_idx)
        R0i = expand(two_R0i / 2)
        R0i_target = -2 * diff(diff(psi, t), coords[i_idx])
        diff_R0i = simplify(R0i - R0i_target)
        print(f"R_0{i_name} = {R0i}")
        print(f"Target = -2 d_{i_name} dot(psi)")
        print(f"Difference = {diff_R0i}")
        assert diff_R0i == 0, f"FAIL: R_0{i_name} mismatch"
        print(f"PASS: R_0{i_name} = -2 d_{i_name} dot(psi)")
        print()

    # --- Ricci scalar R ---
    # R = eta^{mu nu} R_{mu nu}
    # But we have 2*R_{mu nu}, so 2*R = eta^{mu nu} (2*R_{mu nu})
    # More directly: R = d_mu d_nu h^{mu nu} - Box h
    # where h^{mu nu} is the fully raised perturbation
    # d_mu d_nu h^{mu nu}:
    div_div = 0
    for mu in range(4):
        for nu in range(4):
            if h_up[mu, nu] != 0:
                div_div += diff(diff(h_up[mu, nu], coords[mu]), coords[nu])
    div_div = expand(div_div)

    box_h = box(trace_h)

    R_scalar = expand(div_div - box_h)
    print(f"d_mu d_nu h^{{mu nu}} = {div_div}")
    print(f"Box h = {box_h}")
    print(f"R = {R_scalar}")

    R_target = 2*laplacian(Phi) - 4*laplacian(psi) + 6*diff(psi, t, 2)
    diff_R = simplify(R_scalar - R_target)
    print(f"Target R = 2 nabla^2 Phi - 4 nabla^2 psi + 6 ddot(psi)")
    print(f"Difference = {diff_R}")
    assert diff_R == 0, f"FAIL: R mismatch, diff = {diff_R}"
    print("PASS: R = 2 nabla^2 Phi - 4 nabla^2 psi + 6 ddot(psi)")
    print()

    # --- Cross-check: compute R via eta^{mu nu} R_{mu nu} ---
    R_via_contraction = 0
    for mu in range(4):
        two_Rmm = ricci_2(mu, mu)
        R_via_contraction += eta_inv[mu, mu] * two_Rmm / 2
    R_via_contraction = expand(R_via_contraction)
    diff_R_cross = simplify(R_via_contraction - R_scalar)
    print(f"R via eta^{{mu nu}} R_{{mu nu}} = {R_via_contraction}")
    print(f"Difference with direct formula = {diff_R_cross}")
    assert diff_R_cross == 0, "FAIL: two methods for R disagree"
    print("PASS: Both methods for R agree")
    print()

    print("ALL TESTS PASSED")
    return 0

if __name__ == "__main__":
    sys.exit(main())
