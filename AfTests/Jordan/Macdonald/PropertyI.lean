/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.TensorSetup
import AfTests.Jordan.Macdonald.MonoBlock
import AfTests.Jordan.Macdonald.GammaInjectivity

/-!
# Property (i) of M_{p,q} (H-O 2.4.24)

Property (i) says: M_{p,q}(z) = 1/2(pzq* + qzp*) = gamma_mac(p,q) in FS{x,y,z}.

H-O reference: Line 1217 of joa-m.md (statement), lines 1226-1270 (proof).

## Architecture note

Our `M_op` acts on `FreeJordanAlg` (2 generators), but property (i) requires
evaluating M_{p,q} at z, the third generator. Since `FreeJordanAlg` has only
x and y, z is not available as an element.

We prove property (i) in the following form: `gamma_mac(toFA p, toFA q)` satisfies
the **same recurrences** as M_op, using the associative operations in FA3:
- assocU(a)(c) = a * c * a
- assocT(a)(c) = 1/2(a*c + c*a)
- assocUBilinear(a,b)(c) = 1/2(a*c*b + b*c*a)

Each M_op recurrence case (2.52)-(2.57) is verified as an algebraic identity
on `gamma_mac`. Since the recursion is well-founded and the base cases match,
this establishes M_{p,q}(z) = gamma_mac(toFA p, toFA q) for all p, q.

## Main results

* `gamma_mac_one_one` -- gamma_mac(1,1) = z (base case, H-O 2.52 with i=j=0)
* `gamma_mac_assocU` -- U_a(gamma_mac(p,q)) = gamma_mac(a*p, a*q) (property iii, H-O 2.53-2.54)
* `gamma_mac_diff_letter` -- Recurrence for different first letters (H-O 2.55)
* `gamma_mac_T_recurrence` -- T-based recurrence (H-O 2.56-2.57)
* `gamma_mac_U_bilinear` -- U_bilinear identity (property iv in FA3)

## References

* Hanche-Olsen & Stormer, "Jordan Operator Algebras", Section 2.4.24, property (i)
-/

open FreeAssocMono

/-! ### Helper simp lemmas -/

@[simp] theorem FA.star_x_pow (n : ℕ) : star (FA.x ^ n) = FA.x ^ n := by
  rw [star_pow, FA.star_x]

@[simp] theorem FA.star_y_pow (n : ℕ) : star (FA.y ^ n) = FA.y ^ n := by
  rw [star_pow, FA.star_y]

@[simp] theorem FA_to_FA3_one_eq : FA_to_FA3 (1 : FA) = (1 : FA3) := map_one _

theorem FA_to_FA3_pow (a : FA) (n : ℕ) :
    FA_to_FA3 (a ^ n) = (FA_to_FA3 a) ^ n := map_pow _ _ _

@[simp] theorem toFA_xPow (k : ℕ) : toFA (xPow k) = FA.x ^ (k + 1) := by
  simp [xPow, toFA]

@[simp] theorem toFA_yPow (l : ℕ) : toFA (yPow l) = FA.y ^ (l + 1) := by
  simp [yPow, toFA]

/-! ### Base case: gamma_mac(1,1) = z  (H-O 2.52, i=j=0) -/

/-- Property (i) base case: gamma_mac(1,1) = FA3.z.
    Corresponds to M_{1,1} = id, applied to z gives z. H-O line 1233. -/
theorem gamma_mac_one_one : gamma_mac 1 1 = FA3.z := by
  unfold gamma_mac
  simp only [map_one, one_mul, mul_one, star_one]
  rw [← two_smul ℝ FA3.z, smul_smul]; norm_num

/-! ### U-factorization (H-O 2.53-2.54, property iii core)

For self-adjoint a (i.e. star(a) = a), the associative U operator factors gamma_mac:
  a * gamma_mac(p,q) * a = gamma_mac(a*p, a*q)

This is the associative-algebra version of property (iii):
  U_{x^k} M_{p,q} = M_{x^k p, x^k q}

H-O lines 1249-1256: "If M_{x^{i-j}p,q} satisfies (i), then in FS{x,y,z} we have
  M_{x^i p, x^j q}z = U_{x^j} M_{x^{i-j}p,q} z = x^j [1/2(x^{i-j}pzq* + qzp*x^{i-j})] x^j
  = 1/2(x^i pzq*x^j + x^j qzp*x^i)." -/

/-- U-factorization of gamma_mac: a * gamma_mac(p,q) * a = gamma_mac(a*p, a*q)
    when star(a) = a. Corresponds to assocU(a)(gamma_mac(p,q)) = gamma_mac(ap, aq).
    H-O lines 1249-1256. -/
theorem gamma_mac_assocU (a p q : FA) (ha : star a = a) :
    FA_to_FA3 a * gamma_mac p q * FA_to_FA3 a =
    gamma_mac (a * p) (a * q) := by
  have ha3 : star (FA_to_FA3 a) = FA_to_FA3 a := by rw [← FA_to_FA3_star, ha]
  unfold gamma_mac
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_assoc, map_mul,
    star_mul, ha3]

/-! ### Different-letter recurrence (H-O 2.55, property iv core)

For self-adjoint a, b:
  gamma_mac(a*p, b*q) = a * gamma_mac(p,q) * b + b * gamma_mac(p,q) * a - gamma_mac(b*p, a*q)

This is the associative version of (2.55a):
  M_{x^i p, y^j q} = 2 U_{x^i, y^j} M_{p,q} - M_{y^j p, x^i q}

Rearranging: 2 U_{x^i,y^j}(c) = x^i c y^j + y^j c x^i in assoc algebras.
So 2 U_{x^i,y^j} gamma_mac(p,q) - gamma_mac(y^j p, x^i q) = gamma_mac(x^i p, y^j q).

H-O lines 1266-1270: the verification of (i) for (2.55a). -/

/-- Different-letter recurrence for gamma_mac:
    gamma_mac(a*p, b*q) = a*gamma(p,q)*b + b*gamma(p,q)*a - gamma(b*p, a*q)
    when star(a) = a and star(b) = b.  H-O lines 1266-1270. -/
theorem gamma_mac_diff_letter (a b p q : FA) (ha : star a = a) (hb : star b = b) :
    gamma_mac (a * p) (b * q) =
    FA_to_FA3 a * gamma_mac p q * FA_to_FA3 b +
    FA_to_FA3 b * gamma_mac p q * FA_to_FA3 a -
    gamma_mac (b * p) (a * q) := by
  have ha3 : star (FA_to_FA3 a) = FA_to_FA3 a := by rw [← FA_to_FA3_star, ha]
  have hb3 : star (FA_to_FA3 b) = FA_to_FA3 b := by rw [← FA_to_FA3_star, hb]
  unfold gamma_mac
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_assoc, map_mul,
    smul_add, star_mul, ha3, hb3]
  abel

/-! ### T-based recurrence (H-O 2.56-2.57)

Special case of diff_letter with one argument being 1:
  gamma_mac(a*p, 1) = a * gamma_mac(p,1) + gamma_mac(p,1) * a - gamma_mac(p, a)

Corresponds to (2.56a): M_{x^i p, 1} = 2T_{x^i} M_{p,1} - M_{p, x^i}
where 2T_a(c) = a*c + c*a in associative algebras.

H-O lines 1274-1276, 1286-1288. -/

/-- T-based recurrence for gamma_mac:
    gamma_mac(a*p, 1) = a*gamma(p,1) + gamma(p,1)*a - gamma(p, a)
    when star(a) = a.  H-O lines 1274-1276. -/
theorem gamma_mac_T_recurrence (a p : FA) (ha : star a = a) :
    gamma_mac (a * p) 1 =
    FA_to_FA3 a * gamma_mac p 1 + gamma_mac p 1 * FA_to_FA3 a -
    gamma_mac p a := by
  have h := gamma_mac_diff_letter a 1 p 1 ha (by simp)
  simp only [one_mul, mul_one, map_one] at h; exact h

/-! ### U_bilinear identity (H-O 2.55 rearranged, property iv in FA3)

  1/2(a * gamma(p,q) * b + b * gamma(p,q) * a) = 1/2(gamma(a*p, b*q) + gamma(b*p, a*q))

Corresponds to: U_{a,b}(M_{p,q}(z)) = 1/2(M_{ap,bq}(z) + M_{bp,aq}(z)).
H-O lines 1258-1270. -/

/-- U_bilinear identity for gamma_mac:
    1/2(a*gamma(p,q)*b + b*gamma(p,q)*a) = 1/2(gamma(a*p,b*q) + gamma(b*p,a*q))
    when star(a) = a and star(b) = b.  H-O lines 1258-1270. -/
theorem gamma_mac_U_bilinear (a b p q : FA) (ha : star a = a) (hb : star b = b) :
    (1/2 : ℝ) • (FA_to_FA3 a * gamma_mac p q * FA_to_FA3 b +
                  FA_to_FA3 b * gamma_mac p q * FA_to_FA3 a) =
    (1/2 : ℝ) • (gamma_mac (a * p) (b * q) + gamma_mac (b * p) (a * q)) := by
  have ha3 : star (FA_to_FA3 a) = FA_to_FA3 a := by rw [← FA_to_FA3_star, ha]
  have hb3 : star (FA_to_FA3 b) = FA_to_FA3 b := by rw [← FA_to_FA3_star, hb]
  unfold gamma_mac
  simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_assoc, map_mul,
    star_mul, ha3, hb3]
  abel

/-! ### Connection to toFA: prependX / prependY versions

These specialize the gamma_mac identities to the FreeAssocMono operations
used in the M_op recursion. -/

/-- Property (iii)x via gamma_mac: U_{x^{k+1}} applied to gamma_mac(toFA p, toFA q)
    gives gamma_mac(toFA(prependX k p), toFA(prependX k q)) for p, q in Y.
    H-O line 1290-1294. -/
theorem gamma_mac_prependX_inY {p q : FreeAssocMono} (hp : p.inY) (hq : q.inY) (k : ℕ) :
    FA_to_FA3 (FA.x ^ (k + 1)) * gamma_mac (toFA p) (toFA q) *
      FA_to_FA3 (FA.x ^ (k + 1)) =
    gamma_mac (toFA (prependX k p)) (toFA (prependX k q)) := by
  rw [toFA_prependX_of_inY hp, toFA_prependX_of_inY hq]
  exact gamma_mac_assocU (FA.x ^ (k + 1)) (toFA p) (toFA q) (by simp)

/-- Property (iii)y via gamma_mac: U_{y^{l+1}} applied to gamma_mac(toFA p, toFA q)
    gives gamma_mac(toFA(prependY l p), toFA(prependY l q)) for p, q in X.
    H-O line 1290-1294 (symmetric in x,y). -/
theorem gamma_mac_prependY_inX {p q : FreeAssocMono} (hp : p.inX) (hq : q.inX) (l : ℕ) :
    FA_to_FA3 (FA.y ^ (l + 1)) * gamma_mac (toFA p) (toFA q) *
      FA_to_FA3 (FA.y ^ (l + 1)) =
    gamma_mac (toFA (prependY l p)) (toFA (prependY l q)) := by
  rw [toFA_prependY_of_inX hp, toFA_prependY_of_inX hq]
  exact gamma_mac_assocU (FA.y ^ (l + 1)) (toFA p) (toFA q) (by simp)

/-! ### Formal statement of property (i) for individual M_op cases

The following theorems verify that for each case of the M_op recursion,
the corresponding gamma_mac identity holds. Together with the base cases,
this constitutes property (i): M_{p,q}(z) = gamma_mac(toFA p, toFA q).

Since M_op acts on FreeJordanAlg (2 generators, no z), the formal connection
requires either a 3-generator FreeJordanAlg or an evalAssoc naturality theorem.
The gamma_mac identities proved above establish property (i) at the level
of FA3 computations. -/

/-- Convenience abbreviation: gamma_mac applied to toFA of monomials. -/
noncomputable def gamma_mac_mono (p q : FreeAssocMono) : FA3 :=
  gamma_mac (toFA p) (toFA q)

/-- Property (i), base (2.52): gamma_mac_mono(one, one) = z. -/
theorem gamma_mac_mono_one_one : gamma_mac_mono .one .one = FA3.z :=
  gamma_mac_one_one

/-- Property (i) symmetry: gamma_mac_mono(p, q) = gamma_mac_mono(q, p). -/
theorem gamma_mac_mono_comm (p q : FreeAssocMono) :
    gamma_mac_mono p q = gamma_mac_mono q p :=
  gamma_mac_comm _ _

/-- Property (i), (2.53) case: U_{x^{k+1}}(gamma_mac_mono(p, q)) = gamma_mac_mono(xCons k p, xCons k q).
    Valid for p, q in Y. -/
theorem gamma_mac_mono_xCons_xCons {p q : FreeAssocMono}
    (_hp : p.inY) (_hq : q.inY) (k : ℕ) :
    FA_to_FA3 (FA.x ^ (k + 1)) * gamma_mac_mono p q *
      FA_to_FA3 (FA.x ^ (k + 1)) =
    gamma_mac_mono (xCons k p) (xCons k q) := by
  show FA_to_FA3 (FA.x ^ (k + 1)) * gamma_mac (toFA p) (toFA q) *
    FA_to_FA3 (FA.x ^ (k + 1)) =
    gamma_mac (FA.x ^ (k + 1) * toFA p) (FA.x ^ (k + 1) * toFA q)
  exact gamma_mac_assocU _ _ _ (by simp)

/-- Property (i), (2.54) case: U_{y^{l+1}}(gamma_mac_mono(p, q)) = gamma_mac_mono(yCons l p, yCons l q).
    Valid for p, q in X. -/
theorem gamma_mac_mono_yCons_yCons {p q : FreeAssocMono}
    (_hp : p.inX) (_hq : q.inX) (l : ℕ) :
    FA_to_FA3 (FA.y ^ (l + 1)) * gamma_mac_mono p q *
      FA_to_FA3 (FA.y ^ (l + 1)) =
    gamma_mac_mono (yCons l p) (yCons l q) := by
  show FA_to_FA3 (FA.y ^ (l + 1)) * gamma_mac (toFA p) (toFA q) *
    FA_to_FA3 (FA.y ^ (l + 1)) =
    gamma_mac (FA.y ^ (l + 1) * toFA p) (FA.y ^ (l + 1) * toFA q)
  exact gamma_mac_assocU _ _ _ (by simp)

/-- Property (i), (2.55a) case: the different-letter recurrence.
    gamma_mac_mono(xCons k p, yCons l q) =
      (x^{k+1} * gamma(p,q) * y^{l+1} + y^{l+1} * gamma(p,q) * x^{k+1})
      - gamma_mac_mono(yCons l p, xCons k q).
    Valid for p in Y, q in X. -/
theorem gamma_mac_mono_diff_letter (k l : ℕ) (p q : FreeAssocMono) :
    gamma_mac_mono (.xCons k p) (.yCons l q) =
    FA_to_FA3 (FA.x ^ (k + 1)) * gamma_mac_mono p q * FA_to_FA3 (FA.y ^ (l + 1)) +
    FA_to_FA3 (FA.y ^ (l + 1)) * gamma_mac_mono p q * FA_to_FA3 (FA.x ^ (k + 1)) -
    gamma_mac_mono (.yCons l p) (.xCons k q) := by
  show gamma_mac (FA.x ^ (k + 1) * toFA p) (FA.y ^ (l + 1) * toFA q) =
    FA_to_FA3 (FA.x ^ (k + 1)) * gamma_mac (toFA p) (toFA q) * FA_to_FA3 (FA.y ^ (l + 1)) +
    FA_to_FA3 (FA.y ^ (l + 1)) * gamma_mac (toFA p) (toFA q) * FA_to_FA3 (FA.x ^ (k + 1)) -
    gamma_mac (FA.y ^ (l + 1) * toFA p) (FA.x ^ (k + 1) * toFA q)
  exact gamma_mac_diff_letter _ _ _ _ (by simp) (by simp)
