#!/usr/bin/env python3
"""
Verify modular data relations for Z(Fib ⊠ Ising).

S and T matrices from TensorCategories.jl (modular_data_fib_ising_v2.txt).
The entries are polynomials in x where x = √2 - ϕ (ϕ = golden ratio),
satisfying x⁴ + 2x³ - 5x² - 6x - 1 = 0.

Standard MTC relations (for unnormalized S̃):
  (1) S̃ = S̃ᵀ              (symmetry)
  (2) S̃² = D² · C          (C = charge conjugation permutation matrix)
  (3) (S̃T)³ = p₊ · S̃²     where p₊ = Σᵢ θᵢ dᵢ²
  (4) All twists θᵢ are roots of unity
"""

import numpy as np

# ---- Number field setup ----
# x = √2 - ϕ, where ϕ = (1+√5)/2
phi = (1 + np.sqrt(5)) / 2
sqrt2 = np.sqrt(2)
x = sqrt2 - phi  # ≈ -0.20381

# Verify minimal polynomial
assert abs(x**4 + 2*x**3 - 5*x**2 - 6*x - 1) < 1e-12, "minimal poly check failed"

# Verify ϕ and √2 recovery from x
phi_check = (-2*x**3 - 3*x**2 + 10*x + 7) / 3
sqrt2_check = (-2*x**3 - 3*x**2 + 13*x + 7) / 3
assert abs(phi_check - phi) < 1e-12, f"phi recovery: {phi_check} vs {phi}"
assert abs(sqrt2_check - sqrt2) < 1e-12, f"sqrt2 recovery: {sqrt2_check} vs {sqrt2}"
print(f"x = √2 - ϕ = {x:.10f}")
print(f"ϕ = {phi:.10f}, √2 = {sqrt2:.10f}")

# ---- Build S matrix ----
def p(coeffs):
    """Evaluate polynomial a0 + a1*x + a2*x² + a3*x³"""
    return sum(c * x**i for i, c in enumerate(coeffs))

S = np.zeros((15, 15))

# Row 1
S[0,:] = [1, 1, p([10/3, 10/3, -1, -2/3]), p([20/3, 20/3, -2, -4/3]), p([10/3, 10/3, -1, -2/3]), 2, p([20/3, 20/3, -2, -4/3]), 2, p([-28/3, -52/3, 4, 8/3]), p([-20, -24, 8, 4]), p([-14/3, -20/3, 2, 4/3]), p([-28/3, -40/3, 4, 8/3]), p([-14/3, -20/3, 2, 4/3]), p([-28/3, -40/3, 4, 8/3]), p([64/3, 40/3, -8, -8/3])]
# Row 2
S[1,:] = [1, 1, p([10/3, 10/3, -1, -2/3]), p([20/3, 20/3, -2, -4/3]), p([10/3, 10/3, -1, -2/3]), 2, p([20/3, 20/3, -2, -4/3]), 2, p([28/3, 52/3, -4, -8/3]), p([20, 24, -8, -4]), p([-14/3, -20/3, 2, 4/3]), p([-28/3, -40/3, 4, 8/3]), p([-14/3, -20/3, 2, 4/3]), p([-28/3, -40/3, 4, 8/3]), p([-64/3, -40/3, 8, 8/3])]
# Row 3
S[2,:] = [p([10/3, 10/3, -1, -2/3]), p([10/3, 10/3, -1, -2/3]), 1, 2, 1, p([20/3, 20/3, -2, -4/3]), 2, p([20/3, 20/3, -2, -4/3]), p([20, 24, -8, -4]), p([28/3, 52/3, -4, -8/3]), p([14/3, 20/3, -2, -4/3]), p([28/3, 40/3, -4, -8/3]), p([14/3, 20/3, -2, -4/3]), p([28/3, 40/3, -4, -8/3]), p([64/3, 40/3, -8, -8/3])]
# Row 4
S[3,:] = [p([20/3, 20/3, -2, -4/3]), p([20/3, 20/3, -2, -4/3]), 2, 0, 2, 0, -4, p([-40/3, -40/3, 4, 8/3]), 0, 0, p([28/3, 40/3, -4, -8/3]), 0, p([28/3, 40/3, -4, -8/3]), p([-56/3, -80/3, 8, 16/3]), 0]
# Row 5
S[4,:] = [p([10/3, 10/3, -1, -2/3]), p([10/3, 10/3, -1, -2/3]), 1, 2, 1, p([20/3, 20/3, -2, -4/3]), 2, p([20/3, 20/3, -2, -4/3]), p([-20, -24, 8, 4]), p([-28/3, -52/3, 4, 8/3]), p([14/3, 20/3, -2, -4/3]), p([28/3, 40/3, -4, -8/3]), p([14/3, 20/3, -2, -4/3]), p([28/3, 40/3, -4, -8/3]), p([-64/3, -40/3, 8, 8/3])]
# Row 6
S[5,:] = [2, 2, p([20/3, 20/3, -2, -4/3]), 0, p([20/3, 20/3, -2, -4/3]), 0, p([-40/3, -40/3, 4, 8/3]), -4, 0, 0, p([-28/3, -40/3, 4, 8/3]), 0, p([-28/3, -40/3, 4, 8/3]), p([56/3, 80/3, -8, -16/3]), 0]
# Row 7
S[6,:] = [p([20/3, 20/3, -2, -4/3]), p([20/3, 20/3, -2, -4/3]), 2, -4, 2, p([-40/3, -40/3, 4, 8/3]), 4, p([40/3, 40/3, -4, -8/3]), 0, 0, p([28/3, 40/3, -4, -8/3]), p([-56/3, -80/3, 8, 16/3]), p([28/3, 40/3, -4, -8/3]), p([56/3, 80/3, -8, -16/3]), 0]

# Careful with row 7: S[7,7] — need to re-read
# S[7,:] has: ..., 4, p([-40/3, ...]), ...
# Let me re-read:
# S[7,:] = [..., 8//3*x^3 + 4*x^2 - 40//3*x - 40//3, 4, -8//3*x^3 - 4*x^2 + 40//3*x + 40//3, ...]
# Wait I need to be more careful. Let me redo row 7.
# S[7,:] = [-4//3*x^3 - 2*x^2 + 20//3*x + 20//3, same, 2, -4, 2,
#           8//3*x^3 + 4*x^2 - 40//3*x - 40//3,
#           4,
#           -8//3*x^3 - 4*x^2 + 40//3*x + 40//3,
#           0, 0,
#           -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,
#           16//3*x^3 + 8*x^2 - 80//3*x - 56//3,
#           -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,
#           -16//3*x^3 - 8*x^2 + 80//3*x + 56//3,
#           0]

# Fix row 7 (index 6):
S[6,:] = [p([20/3, 20/3, -2, -4/3]), p([20/3, 20/3, -2, -4/3]), 2, -4, 2,
          p([-40/3, -40/3, 4, 8/3]), 4, p([40/3, 40/3, -4, -8/3]),
          0, 0,
          p([28/3, 40/3, -4, -8/3]), p([-56/3, -80/3, 8, 16/3]),
          p([28/3, 40/3, -4, -8/3]), p([56/3, 80/3, -8, -16/3]),  # WAIT: need to re-check sign
          0]

# I realize I need to be more careful. Let me re-parse directly from the file.
# Will rewrite below after careful parsing.

# ========================================================================
# CAREFUL RE-PARSE of all S matrix rows from the data file
# Convention: p([a0, a1, a2, a3]) = a0 + a1*x + a2*x² + a3*x³
# ========================================================================

S = np.zeros((15, 15))

# Define recurring polynomial values
A = p([10/3, 10/3, -1, -2/3])      # -2//3*x^3 - x^2 + 10//3*x + 10//3  (= ϕ+1 ≈ 2.618)
B = p([20/3, 20/3, -2, -4/3])      # -4//3*x^3 - 2*x^2 + 20//3*x + 20//3 (= 2(ϕ+1) ≈ 5.236)
C9 = p([-28/3, -52/3, 4, 8/3])     # 8//3*x^3 + 4*x^2 - 52//3*x - 28//3
D9 = p([-20, -24, 8, 4])           # 4*x^3 + 8*x^2 - 24*x - 20
E = p([-14/3, -20/3, 2, 4/3])      # 4//3*x^3 + 2*x^2 - 20//3*x - 14//3
F = p([-28/3, -40/3, 4, 8/3])      # 8//3*x^3 + 4*x^2 - 40//3*x - 28//3
G = p([64/3, 40/3, -8, -8/3])      # -8//3*x^3 - 8*x^2 + 40//3*x + 64//3
H = p([-40/3, -40/3, 4, 8/3])      # 8//3*x^3 + 4*x^2 - 40//3*x - 40//3 (= 2(ϕ+1)·(-1)? or B-4)
I_val = p([28/3, 40/3, -4, -8/3])  # -8//3*x^3 - 4*x^2 + 40//3*x + 28//3
J = p([-56/3, -80/3, 8, 16/3])     # 16//3*x^3 + 8*x^2 - 80//3*x - 56//3
K_val = p([40/3, 40/3, -4, -8/3])  # -8//3*x^3 - 4*x^2 + 40//3*x + 40//3

# Print key values for sanity
print(f"\nKey polynomial values:")
print(f"  A = ϕ+1 = {A:.6f} (expect {phi+1:.6f})")
print(f"  B = 2(ϕ+1) = {B:.6f} (expect {2*(phi+1):.6f})")
print(f"  E = {E:.6f}")
print(f"  F = {F:.6f}")
print(f"  G = {G:.6f}")

# S[1,:]
S[0] = [1, 1, A, B, A, 2, B, 2, C9, D9, E, F, E, F, G]
# S[2,:]  — same as S[1,:] except cols 9,10,15 sign-flipped
S[1] = [1, 1, A, B, A, 2, B, 2, -C9, -D9, E, F, E, F, -G]
# S[3,:]
S[2] = [A, A, 1, 2, 1, B, 2, B, D9, C9, -E, -F, -E, -F, G]

# Wait — re-read S[3,:] from file:
# S[3,:] = [-2//3*x^3 - x^2 + 10//3*x + 10//3, same, 1, 2, 1,
#           -4//3*x^3 - 2*x^2 + 20//3*x + 20//3,
#           2, -4//3*x^3 - 2*x^2 + 20//3*x + 20//3,
#           -4*x^3 - 8*x^2 + 24*x + 20,    ← = -D9
#           -8//3*x^3 - 4*x^2 + 52//3*x + 28//3,  ← = -C9
#           -4//3*x^3 - 2*x^2 + 20//3*x + 14//3,  ← NOTE: +14/3 not -14/3
#           ...

# Hmm, I see the S[3] col 11 entry is "-4//3*x^3 - 2*x^2 + 20//3*x + 14//3"
# = p([14/3, 20/3, -2, -4/3]) which is different from E = p([-14/3, -20/3, 2, 4/3])
# Actually E = 4//3*x^3 + 2*x^2 - 20//3*x - 14//3 = p([-14/3, -20/3, 2, 4/3])
# And this is -4//3*x^3 - 2*x^2 + 20//3*x + 14//3 = p([14/3, 20/3, -2, -4/3]) = -E
# So col 11 of S[3] = -E. Same pattern for col 12: -F. OK.

# Let me define -E as mE etc for clarity
# S[3,:] = [A, A, 1, 2, 1, B, 2, B, -D9, -C9, -E, -F, -E, -F, G]

# Wait that doesn't match either. Let me re-read VERY carefully from the file.

# Actually I'm making errors with all the signs. Let me just re-parse every entry from scratch.
# This is error-prone by hand. Let me do it programmatically.

print("\n" + "="*70)
print("Re-parsing S matrix from file (programmatic)")
print("="*70)

# I'll define each row directly from the data file entries
# Each entry is a polynomial in x = √2 - ϕ

def make_row(entries_str):
    """Parse a list of polynomial strings into numerical values."""
    # This is complex to do generically; let me just hardcode the matrix.
    pass

# Let me just directly evaluate each entry from the original file format.
# The pattern is: coefficients of 1, x, x², x³

# I'll build the matrix entry by entry from the data file.
# Format: (const, coeff_x, coeff_x2, coeff_x3)

rows = [
    # Row 1 (S[1,:])
    [(1,0,0,0), (1,0,0,0), (10/3,10/3,-1,-2/3), (20/3,20/3,-2,-4/3), (10/3,10/3,-1,-2/3), (2,0,0,0), (20/3,20/3,-2,-4/3), (2,0,0,0), (-28/3,-52/3,4,8/3), (-20,-24,8,4), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (64/3,40/3,-8,-8/3)],
    # Row 2 (S[2,:])
    [(1,0,0,0), (1,0,0,0), (10/3,10/3,-1,-2/3), (20/3,20/3,-2,-4/3), (10/3,10/3,-1,-2/3), (2,0,0,0), (20/3,20/3,-2,-4/3), (2,0,0,0), (28/3,52/3,-4,-8/3), (20,24,-8,-4), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (-64/3,-40/3,8,8/3)],
    # Row 3 (S[3,:])
    [(10/3,10/3,-1,-2/3), (10/3,10/3,-1,-2/3), (1,0,0,0), (2,0,0,0), (1,0,0,0), (20/3,20/3,-2,-4/3), (2,0,0,0), (20/3,20/3,-2,-4/3), (20,24,-8,-4), (28/3,52/3,-4,-8/3), (14/3,20/3,-2,-4/3), (28/3,40/3,-4,-8/3), (14/3,20/3,-2,-4/3), (28/3,40/3,-4,-8/3), (64/3,40/3,-8,-8/3)],
    # Row 4 (S[4,:])
    [(20/3,20/3,-2,-4/3), (20/3,20/3,-2,-4/3), (2,0,0,0), (0,0,0,0), (2,0,0,0), (0,0,0,0), (-4,0,0,0), (-40/3,-40/3,4,8/3), (0,0,0,0), (0,0,0,0), (28/3,40/3,-4,-8/3), (0,0,0,0), (28/3,40/3,-4,-8/3), (-56/3,-80/3,8,16/3), (0,0,0,0)],
    # Row 5 (S[5,:])
    [(10/3,10/3,-1,-2/3), (10/3,10/3,-1,-2/3), (1,0,0,0), (2,0,0,0), (1,0,0,0), (20/3,20/3,-2,-4/3), (2,0,0,0), (20/3,20/3,-2,-4/3), (-20,-24,8,4), (-28/3,-52/3,4,8/3), (14/3,20/3,-2,-4/3), (28/3,40/3,-4,-8/3), (14/3,20/3,-2,-4/3), (28/3,40/3,-4,-8/3), (-64/3,-40/3,8,8/3)],
    # Row 6 (S[6,:])
    [(2,0,0,0), (2,0,0,0), (20/3,20/3,-2,-4/3), (0,0,0,0), (20/3,20/3,-2,-4/3), (0,0,0,0), (-40/3,-40/3,4,8/3), (-4,0,0,0), (0,0,0,0), (0,0,0,0), (-28/3,-40/3,4,8/3), (0,0,0,0), (-28/3,-40/3,4,8/3), (56/3,80/3,-8,-16/3), (0,0,0,0)],
    # Row 7 (S[7,:])
    [(20/3,20/3,-2,-4/3), (20/3,20/3,-2,-4/3), (2,0,0,0), (-4,0,0,0), (2,0,0,0), (-40/3,-40/3,4,8/3), (4,0,0,0), (40/3,40/3,-4,-8/3), (0,0,0,0), (0,0,0,0), (28/3,40/3,-4,-8/3), (-56/3,-80/3,8,16/3), (28/3,40/3,-4,-8/3), (56/3,80/3,-8,-16/3), (0,0,0,0)],
    # Row 8 (S[8,:])
    [(2,0,0,0), (2,0,0,0), (20/3,20/3,-2,-4/3), (-40/3,-40/3,4,8/3), (20/3,20/3,-2,-4/3), (-4,0,0,0), (40/3,40/3,-4,-8/3), (4,0,0,0), (0,0,0,0), (0,0,0,0), (-28/3,-40/3,4,8/3), (56/3,80/3,-8,-16/3), (-28/3,-40/3,4,8/3), (-56/3,-80/3,8,16/3), (0,0,0,0)],
    # Row 9 (S[9,:])
    [(-28/3,-52/3,4,8/3), (28/3,52/3,-4,-8/3), (20,24,-8,-4), (0,0,0,0), (-20,-24,8,4), (0,0,0,0), (0,0,0,0), (0,0,0,0), (0,0,0,0), (0,0,0,0), (64/3,40/3,-8,-8/3), (0,0,0,0), (-64/3,-40/3,8,8/3), (0,0,0,0), (0,0,0,0)],
    # Row 10 (S[10,:])
    [(-20,-24,8,4), (20,24,-8,-4), (28/3,52/3,-4,-8/3), (0,0,0,0), (-28/3,-52/3,4,8/3), (0,0,0,0), (0,0,0,0), (0,0,0,0), (0,0,0,0), (0,0,0,0), (-64/3,-40/3,8,8/3), (0,0,0,0), (64/3,40/3,-8,-8/3), (0,0,0,0), (0,0,0,0)],
    # Row 11 (S[11,:])
    [(-14/3,-20/3,2,4/3), (-14/3,-20/3,2,4/3), (14/3,20/3,-2,-4/3), (28/3,40/3,-4,-8/3), (14/3,20/3,-2,-4/3), (-28/3,-40/3,4,8/3), (28/3,40/3,-4,-8/3), (-28/3,-40/3,4,8/3), (64/3,40/3,-8,-8/3), (-64/3,-40/3,8,8/3), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (-14/3,-20/3,2,4/3), (-28/3,-40/3,4,8/3), (64/3,40/3,-8,-8/3)],

    # Wait - re-read row 11 from file:
    # S[11,:] = [4//3*x^3 + 2*x^2 - 20//3*x - 14//3, same,
    #   -4//3*x^3 - 2*x^2 + 20//3*x + 14//3,    ← col3
    #   -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,     ← col4
    #   -4//3*x^3 - 2*x^2 + 20//3*x + 14//3,    ← col5
    #   8//3*x^3 + 4*x^2 - 40//3*x - 28//3,      ← col6
    #   -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,     ← col7
    #   8//3*x^3 + 4*x^2 - 40//3*x - 28//3,      ← col8
    #   -8//3*x^3 - 8*x^2 + 40//3*x + 64//3,     ← col9
    #   8//3*x^3 + 8*x^2 - 40//3*x - 64//3,      ← col10
    #   -4//3*x^3 - 2*x^2 + 20//3*x + 14//3,     ← col11
    #   -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,     ← col12
    #   -4//3*x^3 - 2*x^2 + 20//3*x + 14//3,     ← col13
    #   -8//3*x^3 - 4*x^2 + 40//3*x + 28//3,     ← col14
    #   8//3*x^3 + 8*x^2 - 40//3*x - 64//3]      ← col15
    #
    # col 6: 8//3*x^3 + 4*x^2 - 40//3*x - 28//3 — this is the NEGATIVE of what I had
    # Let me fix. The pattern from file is:
    # "8//3*x^3 + 4*x^2 - 40//3*x - 28//3" = p([-28/3, -40/3, 4, 8/3]) = F (as defined above)

    # OK wait. I see I already have the wrong sign for some entries in row 11.
    # Let me carefully re-read from the original file and use a different approach.
]

# ========================================================================
# STOP. Manual transcription is too error-prone with 225 polynomial entries.
# Let me parse the data file directly.
# ========================================================================

import re

print("\n" + "="*70)
print("PARSING S AND T FROM DATA FILE")
print("="*70)

with open("/home/tobiasosborne/Projects/af-tests/examples10/modular_data_fib_ising_v2.txt") as f:
    lines = f.readlines()

S = np.zeros((15, 15))
T = np.zeros(15)

def eval_expr(expr_str):
    """Evaluate a polynomial expression in x."""
    expr_str = expr_str.strip()
    if not expr_str:
        return 0.0
    # Replace x^n with x**n for Python eval
    s = expr_str.replace('^', '**')
    # Replace // with / for Python (these are exact fractions in Julia)
    # But careful: 2//3 means Rational(2,3) in Julia = 2/3 in Python
    s = re.sub(r'(\d+)//(\d+)', r'(\1/\2)', s)
    try:
        return eval(s, {"x": x, "__builtins__": {}})
    except Exception as e:
        print(f"  ERROR evaluating '{expr_str}' -> '{s}': {e}")
        return float('nan')

for line in lines:
    line = line.strip()
    # Parse S matrix rows
    m = re.match(r'S\[(\d+),:\]\s*=\s*\[(.*)\]', line)
    if m:
        row = int(m.group(1)) - 1
        entries = m.group(2).split(',')
        for col, entry in enumerate(entries):
            S[row, col] = eval_expr(entry)

    # Parse T diagonal
    m = re.match(r'T\[(\d+)\]\s*=\s*(.*)', line)
    if m:
        idx = int(m.group(1)) - 1
        T[idx] = eval_expr(m.group(2))

print(f"\nS matrix parsed: shape {S.shape}")
print(f"T diagonal parsed: {T}")

# ---- FP dimensions ----
# From the data file header
# Need to evaluate the FPdim entries too. Let me compute from the S matrix.
# In an MTC, d_i = S_{0,i}/S_{0,0}, but this uses normalized S.
# For unnormalized S̃: d_i = S̃_{0,i}/S̃_{0,0}
d = S[0, :] / S[0, 0]
print(f"\nQuantum dimensions d_i = S[0,i]/S[0,0]:")
for i, di in enumerate(d):
    print(f"  d_{i+1} = {di:.6f}")

D2 = np.sum(d**2)
print(f"\nD² = Σ d_i² = {D2:.6f}")
# Expected: FPdim²(Z) = 209.443
print(f"Expected D² ≈ 209.443")

# ---- CHECK 1: Symmetry ----
print("\n" + "="*70)
print("CHECK 1: S = Sᵀ (symmetry)")
print("="*70)
diff_sym = np.max(np.abs(S - S.T))
print(f"  max|S - Sᵀ| = {diff_sym:.2e}")
if diff_sym < 1e-10:
    print("  PASS ✓")
else:
    print("  FAIL ✗")
    # Show where asymmetry occurs
    for i in range(15):
        for j in range(i+1, 15):
            d = abs(S[i,j] - S[j,i])
            if d > 1e-10:
                print(f"    S[{i+1},{j+1}] = {S[i,j]:.6f}, S[{j+1},{i+1}] = {S[j,i]:.6f}, diff = {d:.2e}")

# ---- CHECK 2: S² ∝ C (charge conjugation) ----
print("\n" + "="*70)
print("CHECK 2: S² = D² · C")
print("="*70)
S2 = S @ S
# Normalize: S²/D² should be a permutation matrix (charge conjugation)
S2_norm = S2 / (S[0,0]**2 * D2)  # Wait, need to be careful about normalization
# Actually for unnormalized S̃, S̃² should equal (S̃_{0,0})² · D² · C
# Or more simply: (S̃/S̃_{0,0})² should equal D² · C
# No — let me think again.
# If s = S̃/D is the normalized S matrix, then s² = C.
# So S̃² = D² · C.
# D² = Σ d_i² where d_i = S̃_{0,i}/S̃_{0,0}.
# But actually D² = FPdim²(Z) is computed with the actual quantum dims,
# and the relation is s_{ij} = S̃_{ij}/D, so s² = C means S̃²/D² = C,
# i.e., S̃² = D² · C.
# But wait, D² = Σ d_i² = Σ (S̃_{0,i}/S̃_{0,0})² = (1/S̃_{0,0}²) · Σ S̃_{0,i}²
# and also Σ S̃_{0,i}² = (S̃²)_{0,0} (from matrix mult, since S̃ symmetric)
# So D² = (S̃²)_{0,0} / S̃_{0,0}²

# For a modular category, S̃_{0,0} = 1 (the trace of id on unit object).
# So D² = (S̃²)_{0,0}.

S2_00 = S2[0, 0]
print(f"  (S²)[0,0] = {S2_00:.6f}")
print(f"  D² from dims = {D2:.6f}")
print(f"  S[0,0] = {S[0,0]:.6f}")

# Check if S² is proportional to a permutation matrix
# S² / S2_00 should have exactly one 1 in each row (charge conjugation)
S2_scaled = S2 / S2_00
print(f"\n  S²/S²[0,0] (should be permutation matrix C):")
for i in range(15):
    row = S2_scaled[i]
    nonzero = [(j, row[j]) for j in range(15) if abs(row[j]) > 1e-6]
    print(f"    Row {i+1}: {nonzero}")

# ---- CHECK 3: T matrix properties ----
print("\n" + "="*70)
print("CHECK 3: T diagonal — roots of unity?")
print("="*70)
for i in range(15):
    theta = T[i]
    if abs(theta) < 1e-10:
        print(f"  T[{i+1}] = {theta:.6f}  ← ZERO (problem!)")
    else:
        # Check |θ| = 1
        print(f"  T[{i+1}] = {theta:.6f}, |T| = {abs(theta):.6f}", end="")
        if abs(abs(theta) - 1) < 1e-10:
            # Find the angle
            angle = np.angle(theta) / (2 * np.pi)
            print(f", angle/2π = {angle:.6f} ✓")
        else:
            print(f" ← NOT unit modulus!")

# ---- CHECK 4: (ST)³ relation ----
print("\n" + "="*70)
print("CHECK 4: (ST)³ = p₊ · S²")
print("="*70)

T_mat = np.diag(T)
ST = S @ T_mat
ST3 = ST @ ST @ ST

# p₊ = Σ θ_i d_i² (using unnormalized dims = S̃[0,i])
# Actually p₊ = Σ θ_i d_i² where d_i are the quantum dims
# For unnormalized: p̃₊ = Σ θ_i S̃_{0,i}²/S̃_{0,0}² = (1/S̃_{0,0}²) Σ θ_i S̃_{0,i}²
unnorm_p_plus = sum(T[i] * S[0,i]**2 for i in range(15))
p_plus = unnorm_p_plus / S[0,0]**2
print(f"  p₊ = Σ θ_i d_i² = {p_plus:.6f}")
print(f"  D = √D² = {np.sqrt(D2):.6f}")
print(f"  p₊/D = {p_plus/np.sqrt(D2):.6f} (should be root of unity for anomaly-free)")

# Check (ST)³ = p₊ · S²
# With unnormalized S̃: (S̃T)³ = p₊ · S̃²
# Hmm, let me derive: s = S̃/D, (sT)³ = (p₊/D)·s² = (p₊/D)·C
# (S̃T/D)³ = (p₊/D)·C → (S̃T)³ = D³·(p₊/D)·C = D²·p₊·C = p₊·S̃²
# So (S̃T)³ = p₊·S̃² where p₊ = Σ θ_i d_i²

ratio = ST3 / S2 if np.max(np.abs(S2)) > 1e-10 else None
if ratio is not None:
    # Check if ratio is constant (= p₊)
    nonzero_mask = np.abs(S2) > 1e-6
    ratios = ST3[nonzero_mask] / S2[nonzero_mask]
    if len(ratios) > 0:
        print(f"\n  (ST)³ / S² ratios (should all be p₊ = {p_plus:.6f}):")
        print(f"    min = {np.min(ratios):.6f}")
        print(f"    max = {np.max(ratios):.6f}")
        print(f"    std = {np.std(ratios):.2e}")
        if np.std(ratios) < 1e-6:
            print(f"    PASS ✓ — ratio is constant = {np.mean(ratios):.6f}")
        else:
            print(f"    FAIL ✗ — ratio varies")

# Also check where S² is zero, (ST)³ should also be zero
zero_mask = np.abs(S2) < 1e-6
st3_at_zero = ST3[zero_mask]
print(f"\n  Where S²≈0: max|(ST)³| = {np.max(np.abs(st3_at_zero)):.2e}" if len(st3_at_zero) > 0 else "")

# ---- CHECK 5: S² structure (find charge conjugation) ----
print("\n" + "="*70)
print("CHECK 5: Charge conjugation from S²")
print("="*70)
# If S² = D²·C, then C = S²/D². Check C is a permutation.
if abs(S2_00) > 1e-6:
    C_mat = S2 / S2_00
    print("  C = S²/(S²[0,0]):")
    # Check each row has exactly one nonzero entry
    is_perm = True
    perm = []
    for i in range(15):
        row = C_mat[i]
        big = [(j, row[j]) for j in range(15) if abs(row[j]) > 0.1]
        if len(big) == 1 and abs(big[0][1] - 1) < 1e-6:
            perm.append(big[0][0])
        else:
            is_perm = False
            perm.append(-1)
            print(f"    Row {i+1}: NOT a permutation row: {big}")

    if is_perm:
        print(f"  C is a permutation: {[p+1 for p in perm]}")
        # Check C² = I
        C2 = C_mat @ C_mat
        print(f"  C² = I? max|C²-I| = {np.max(np.abs(C2 - np.eye(15))):.2e}")
    else:
        print("  S² is NOT proportional to a permutation matrix!")
        print("  This suggests the modular data is inconsistent.")

# ---- Summary ----
print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"  S symmetric:     {'PASS' if diff_sym < 1e-10 else 'FAIL'}")
print(f"  T[9,10,15]=0:    These break modular relations (twists must be roots of unity)")
print(f"  S²=D²·C:         Check output above")
print(f"  (ST)³=p₊·S²:     Check output above")
