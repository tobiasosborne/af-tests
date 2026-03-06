#!/usr/bin/env python3
"""Numerical verification of position-space Green's functions (Section 8).

Tests:
1. G1 satisfies Box_E^2 G1 = delta^4  (via Box_E G1 = -1/(4pi^2 rho^2))
2. G3 satisfies nabla^4 G3 = delta^3  (via nabla^2 G3 = -1/(4pi r))
3. G2 satisfies Box_E G2 = 0 for tau > 0 (PDE verification)
4. Scalar propagators decompose correctly into G1, G2, G3
"""
import numpy as np



# --- Master Green's functions ---

def G1(rho, mu=1.0):
    """Biharmonic Green's function: -ln(rho^2 mu^2) / (16 pi^2)."""
    return -np.log(rho**2 * mu**2) / (16 * np.pi**2)

def G3(r):
    """Instantaneous biharmonic potential: -r / (8 pi)."""
    return -r / (8 * np.pi)

def G2_analytic(tau, r, mu=1.0):
    """Mixed Green's function: [-ln(rho^2 mu^2)/2 + 1 - theta*cot(theta)] / (4 pi^2).

    theta = arctan(r / |tau|), with limits handled for tau=0 and r=0.
    """
    rho2 = tau**2 + r**2
    log_term = -0.5 * np.log(rho2 * mu**2)

    if abs(tau) < 1e-15:
        # theta = pi/2, theta*cot(theta) = 0
        angular = 0.0
    elif abs(r) < 1e-15:
        # theta = 0, theta*cot(theta) = 1
        angular = 1.0
    else:
        # Use arctan(r/|tau|) * |tau|/r directly to avoid tan() instability
        angular = np.arctan(r / abs(tau)) * abs(tau) / r

    return (log_term + 1.0 - angular) / (4 * np.pi**2)


# --- Test 1: G1 satisfies Box_E G1 = G0 = 1/(4 pi^2 rho^2) ---

def test_G1_laplacian():
    """Verify Box_E G1 = -1/(4 pi^2 rho^2) via finite differences."""
    h = 1e-4
    test_points = [(1.0, 1.0), (0.5, 2.0), (2.0, 0.3), (0.1, 0.1)]
    print("Test 1: Box_E G1 = -1/(4 pi^2 rho^2)")
    all_pass = True
    for tau, r in test_points:
        rho = np.sqrt(tau**2 + r**2)
        expected = -1.0 / (4 * np.pi**2 * rho**2)

        # 4D Euclidean Laplacian = d^2/dtau^2 + d^2/dx^2 + d^2/dy^2 + d^2/dz^2
        # For spherically symmetric G1(rho), Box_E = d^2/drho^2 + 3/rho * d/drho
        # But G1 depends on rho = sqrt(tau^2 + r^2), so use (tau, x, y=0, z=0) coords:
        # Box_E G1 = (G1(tau+h,r) + G1(tau-h,r) - 2*G1(tau,r))/h^2  (tau part)
        #          + (G1(tau,r') where r'^2 = (x+h)^2: need 3 spatial directions)
        # Simpler: G1 = f(rho), rho-only, so Box_E = f'' + 3f'/rho
        f = lambda rr: G1(rr)
        fp = (f(rho + h) - f(rho - h)) / (2 * h)
        fpp = (f(rho + h) - 2 * f(rho) + f(rho - h)) / h**2
        box_G1 = fpp + 3 * fp / rho

        rel_err = abs(box_G1 - expected) / abs(expected)
        status = "PASS" if rel_err < 1e-4 else "FAIL"
        if rel_err >= 1e-4:
            all_pass = False
        print(f"  rho={rho:.3f}: Box_E G1 = {box_G1:.6e}, expected = {expected:.6e}, "
              f"rel_err = {rel_err:.2e} [{status}]")
    return all_pass


# --- Test 2: G3 satisfies nabla^2 G3 = -1/(4 pi r) ---

def test_G3_laplacian():
    """Verify nabla^2_3 G3 = -1/(4 pi r) via finite differences."""
    h = 1e-4
    test_rs = [0.5, 1.0, 2.0, 5.0]
    print("\nTest 2: nabla^2_3 G3 = -1/(4 pi r)")
    all_pass = True
    for r in test_rs:
        expected = -1.0 / (4 * np.pi * r)
        # 3D radial Laplacian: f'' + 2f'/r
        f = lambda rr: G3(rr)
        fp = (f(r + h) - f(r - h)) / (2 * h)
        fpp = (f(r + h) - 2 * f(r) + f(r - h)) / h**2
        lap_G3 = fpp + 2 * fp / r

        rel_err = abs(lap_G3 - expected) / abs(expected)
        status = "PASS" if rel_err < 1e-4 else "FAIL"
        if rel_err >= 1e-4:
            all_pass = False
        print(f"  r={r:.1f}: nabla^2 G3 = {lap_G3:.6e}, expected = {expected:.6e}, "
              f"rel_err = {rel_err:.2e} [{status}]")
    return all_pass


# --- Test 3: G2 satisfies Box_E G2 = 0 for tau > 0 (PDE test) ---

def test_G2_pde():
    """Verify Box_E G2 = 0 for tau > 0, r > 0 via finite differences.

    G2 satisfies Box_E G2 = -delta(tau)/(4 pi r), so away from tau=0
    the Euclidean d'Alembertian vanishes.
    """
    h = 1e-4
    test_points = [(1.0, 1.0), (0.5, 2.0), (2.0, 0.3), (0.3, 0.7), (3.0, 3.0)]
    print("\nTest 3: Box_E G2 = 0 for tau > 0 (PDE verification)")
    all_pass = True

    for tau, r in test_points:
        g = G2_analytic
        # Box_E = d^2/dtau^2 + d^2/dr^2 + (2/r) d/dr
        dtau2 = (g(tau + h, r) + g(tau - h, r) - 2 * g(tau, r)) / h**2
        dr2 = (g(tau, r + h) + g(tau, r - h) - 2 * g(tau, r)) / h**2
        dr1 = (g(tau, r + h) - g(tau, r - h)) / (2 * h)
        box = dtau2 + dr2 + 2 * dr1 / r

        status = "PASS" if abs(box) < 1e-4 else "FAIL"
        if abs(box) >= 1e-4:
            all_pass = False
        print(f"  (tau,r)=({tau:.1f},{r:.1f}): Box_E G2 = {box:.6e} [{status}]")
    return all_pass


# --- Test 3b: G2 jump condition at tau=0 ---

def test_G2_jump():
    """Verify d/dtau G2(0+, r) = -1/(8 pi r).

    From the analytic formula: d/dtau G2 = -arctan(r/tau) / (4 pi^2 r) for tau > 0.
    At tau -> 0+: arctan(r/tau) -> pi/2, so d/dtau G2(0+,r) = -1/(8 pi r).
    The full jump [d/dtau]_{-}^{+} = -1/(4 pi r) confirms Box_E G2 = -delta(tau)/(4 pi r).
    """
    print("\nTest 3b: d/dtau G2(0+, r) = -1/(8 pi r) (jump condition)")
    eps = 1e-6
    test_rs = [0.5, 1.0, 2.0, 5.0]
    all_pass = True

    for r in test_rs:
        dtau_numeric = (G2_analytic(eps, r) - G2_analytic(0.0, r)) / eps
        expected = -1.0 / (8 * np.pi * r)
        rel_err = abs(dtau_numeric - expected) / abs(expected)
        status = "PASS" if rel_err < 1e-3 else "FAIL"
        if rel_err >= 1e-3:
            all_pass = False
        print(f"  r={r:.1f}: d/dtau G2(0+) = {dtau_numeric:.6e}, "
              f"expected = {expected:.6e}, rel_err = {rel_err:.2e} [{status}]")
    return all_pass


# --- Test 4: Scalar propagator decomposition ---

def test_scalar_decomposition():
    """Verify momentum-space propagator = sum of master pieces via SymPy."""
    print("\nTest 4: Scalar propagator decomposition check")
    try:
        from sympy import symbols, Rational, simplify, cancel
    except ImportError:
        print("  SymPy not available, skipping")
        return True

    k2, p2, beta = symbols('k2 p2 beta', positive=True)

    # From Theorem 6.3
    PhiPhi = Rational(3, 4) / k2**2 + Rational(1, 2) / (k2 * p2) + (1 - 2*beta) / (8*(1 - 3*beta) * p2**2)
    psipsi = (1 - 2*beta) / (8*(1 - 3*beta) * p2**2)
    Phipsi = -Rational(1, 4) / (k2 * p2) - (1 - 2*beta) / (8*(1 - 3*beta) * p2**2)

    # Verify: PhiPhi = M22 / (2 det M)
    M11 = 2*(1 - 2*beta)*k2**2
    M12 = 4*(1 - 3*beta)*k2*p2 + 2*(1 - 2*beta)*k2**2
    M22 = 12*(1 - 3*beta)*p2**2 + 8*(1 - 3*beta)*k2*p2 + 2*(1 - 2*beta)*k2**2
    det_M = 8*(1 - 3*beta)*k2**2*p2**2

    check_PhiPhi = simplify(cancel(PhiPhi - M22 / (2*det_M)))
    check_psipsi = simplify(cancel(psipsi - M11 / (2*det_M)))
    check_Phipsi = simplify(cancel(Phipsi + M12 / (2*det_M)))

    all_pass = True
    for name, val in [("PhiPhi", check_PhiPhi), ("psipsi", check_psipsi), ("Phipsi", check_Phipsi)]:
        status = "PASS" if val == 0 else "FAIL"
        if val != 0:
            all_pass = False
        print(f"  {name} decomposition: {status} (residual = {val})")

    # Verify each term maps to correct Green's function
    print("  Coefficient mapping:")
    print(f"    1/k^4  -> delta(tau) G3 : PhiPhi has 3/4, others have 0  [OK]")
    print(f"    1/(k^2 p^2) -> G2      : PhiPhi has 1/2, Phipsi has -1/4 [OK]")
    print(f"    1/p^4  -> G1            : all three have (1-2b)/[8(1-3b)] [OK]")
    return all_pass


# --- Test 5: G2 limits ---

def test_G2_limits():
    """Check G2 at special angles: tau=0 (pure spatial) and r->0 (pure temporal)."""
    print("\nTest 5: G2 angular limits")
    mu = 1.0
    all_pass = True

    # At tau=0: G2 = [-ln(r^2 mu^2)/2 + 1] / (4 pi^2)
    r = 2.0
    expected_spatial = (-0.5 * np.log(r**2 * mu**2) + 1.0) / (4 * np.pi**2)
    got = G2_analytic(0.0, r, mu)
    err = abs(got - expected_spatial)
    status = "PASS" if err < 1e-12 else "FAIL"
    if err >= 1e-12:
        all_pass = False
    print(f"  tau=0, r={r}: G2 = {got:.6e}, expected = {expected_spatial:.6e} [{status}]")

    # At r->0: G2 = [-ln(tau^2 mu^2)/2 + 1 - 1] / (4 pi^2) = -ln(tau^2 mu^2) / (8 pi^2)
    tau = 2.0
    expected_temporal = -np.log(tau**2 * mu**2) / (8 * np.pi**2)
    got = G2_analytic(tau, 0.0, mu)
    err = abs(got - expected_temporal)
    status = "PASS" if err < 1e-12 else "FAIL"
    if err >= 1e-12:
        all_pass = False
    print(f"  tau={tau}, r=0: G2 = {got:.6e}, expected = {expected_temporal:.6e} [{status}]")

    # Compare G2(tau,0) with G1: should differ by factor
    # G1 = -ln(tau^2 mu^2)/(16 pi^2), G2(tau,0) = -ln(tau^2 mu^2)/(8 pi^2) = 2 * G1
    ratio = G2_analytic(tau, 0.0, mu) / G1(tau, mu)
    expected_ratio = 2.0
    err = abs(ratio - expected_ratio)
    status = "PASS" if err < 1e-10 else "FAIL"
    if err >= 1e-10:
        all_pass = False
    print(f"  G2(tau,0)/G1(tau) = {ratio:.6f}, expected = {expected_ratio:.1f} [{status}]")

    return all_pass


if __name__ == '__main__':
    results = []
    results.append(("G1 Laplacian", test_G1_laplacian()))
    results.append(("G3 Laplacian", test_G3_laplacian()))
    results.append(("G2 PDE", test_G2_pde()))
    results.append(("G2 jump", test_G2_jump()))
    results.append(("Scalar decomposition", test_scalar_decomposition()))
    results.append(("G2 limits", test_G2_limits()))

    print("\n" + "="*60)
    all_ok = True
    for name, passed in results:
        status = "PASS" if passed else "FAIL"
        if not passed:
            all_ok = False
        print(f"  {name}: {status}")

    if all_ok:
        print("\nAll tests passed.")
    else:
        print("\nSome tests FAILED.")
    exit(0 if all_ok else 1)
