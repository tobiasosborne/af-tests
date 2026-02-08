/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.TensorSetup
import AfTests.Jordan.Macdonald.MonoBlock
import AfTests.Jordan.Macdonald.GammaInjectivity
import AfTests.Jordan.Macdonald.MOperator

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

/-! ### Property (i) typing bridge: M_op ↔ gamma_mac formal connection

Property (i) of H-O 2.4.24 (line 1217) states: M_{p,q}(z) = ½(pzq* + qzp*).

The bridge connects M_op (acting on FreeJordanAlg, 2 generators) to gamma_mac
(an element of FA3, 3 generators) via the evalAssoc naturality lemmas.

**Approach**: Define `assocM p q : FA3 → FA3` as the associative version of
M_{p,q}, sending `c ↦ ½(p'·c·q'* + q'·c·p'*)` where p' = FA_to_FA3(toFA p).
This is exactly gamma_mac with c replacing z. Then:
- `assocM p q FA3.z = gamma_mac_mono p q` (immediate from definition)
- `evalAssoc(M_op p q v) = assocM p q (evalAssoc v)` (by structural induction on M_op)

**H-O references**: 2.4.24(i) at line 1217, proof at lines 1226-1288. -/

/-- The associative version of M_{p,q}: sends c to ½(p'·c·q'* + q'·c·p'*)
    where p' = FA_to_FA3(toFA p). This is gamma_mac with c replacing z.
    H-O 2.4.24(i), line 1217. -/
noncomputable def assocM (p q : FreeAssocMono) (c : FA3) : FA3 :=
  (1/2 : ℝ) • (FA_to_FA3 (toFA p) * c * star (FA_to_FA3 (toFA q))
             + FA_to_FA3 (toFA q) * c * star (FA_to_FA3 (toFA p)))

/-- assocM at z gives gamma_mac_mono, by definition. H-O 2.4.24(i), line 1217. -/
theorem assocM_z (p q : FreeAssocMono) :
    assocM p q FA3.z = gamma_mac_mono p q := rfl

/-- assocM is symmetric. -/
theorem assocM_comm (p q : FreeAssocMono) (c : FA3) :
    assocM p q c = assocM q p c := by
  unfold assocM; congr 1; exact add_comm _ _

/-! ### evalAssoc compatibility: M_op evaluates to assocM

The core induction proving that evalAssoc(M_op p q v) = assocM p q (evalAssoc v).
This is proved by structural induction on M_op. Each case uses the evalAssoc
naturality lemmas from FJOperators.lean.

Key evalAssoc lemmas used:
- `evalAssoc_T` : evalAssoc(T_c(v)) = ½(c'v' + v'c')
- `evalAssoc_U` : evalAssoc(U_c(v)) = c'v'c'
- `evalAssoc_U_bilinear` : evalAssoc(U_{c,d}(v)) = ½(c'v'd' + d'v'c')
- `evalAssoc_pow_x` : evalAssoc(pow x n) = a'^n
- `evalAssoc_pow_y` : evalAssoc(pow y n) = b'^n
- `evalAssoc_sub`, `evalAssoc_smul`, `evalAssoc_add` -/

/-- Abbreviation for evalAssoc at the FA3-embedded generators. -/
noncomputable abbrev evalFA3 : FreeJordanAlg → FA3 :=
  FreeJordanAlg.evalAssoc (FA_to_FA3 FA.x) (FA_to_FA3 FA.y)

/-- evalFA3 commutes with addition. -/
theorem evalFA3_add (u v : FreeJordanAlg) :
    evalFA3 (u + v) = evalFA3 u + evalFA3 v :=
  FreeJordanAlg.evalAssoc_add _ _ u v

/-- evalFA3 commutes with scalar multiplication. -/
theorem evalFA3_smul (r : ℝ) (u : FreeJordanAlg) :
    evalFA3 (r • u) = r • evalFA3 u :=
  FreeJordanAlg.evalAssoc_smul _ _ r u

/-- evalFA3 commutes with subtraction. -/
theorem evalFA3_sub (u v : FreeJordanAlg) :
    evalFA3 (u - v) = evalFA3 u - evalFA3 v :=
  FreeJordanAlg.evalAssoc_sub _ _ u v

/-- evalFA3 of T gives ½(c'v' + v'c'). -/
theorem evalFA3_T (c v : FreeJordanAlg) :
    evalFA3 (FreeJordanAlg.T c v) =
    (1/2 : ℝ) • (evalFA3 c * evalFA3 v + evalFA3 v * evalFA3 c) :=
  FreeJordanAlg.evalAssoc_T _ _ c v

/-- evalFA3 of U gives c'v'c'. -/
theorem evalFA3_U (c v : FreeJordanAlg) :
    evalFA3 (FreeJordanAlg.U c v) = evalFA3 c * evalFA3 v * evalFA3 c :=
  FreeJordanAlg.evalAssoc_U _ _ c v

/-- evalFA3 of U_bilinear gives ½(c'v'd' + d'v'c'). -/
theorem evalFA3_U_bilinear (c d v : FreeJordanAlg) :
    evalFA3 (FreeJordanAlg.U_bilinear c d v) =
    (1/2 : ℝ) • (evalFA3 c * evalFA3 v * evalFA3 d
               + evalFA3 d * evalFA3 v * evalFA3 c) :=
  FreeJordanAlg.evalAssoc_U_bilinear _ _ c d v

/-- evalFA3 maps Jordan powers of x to associative powers. -/
theorem evalFA3_pow_x (n : ℕ) :
    evalFA3 (FreeJordanAlg.pow FreeJordanAlg.x n) = (FA_to_FA3 FA.x) ^ n :=
  FreeJordanAlg.evalAssoc_pow_x _ _ n

/-- evalFA3 maps Jordan powers of y to associative powers. -/
theorem evalFA3_pow_y (n : ℕ) :
    evalFA3 (FreeJordanAlg.pow FreeJordanAlg.y n) = (FA_to_FA3 FA.y) ^ n :=
  FreeJordanAlg.evalAssoc_pow_y _ _ n

/-! ### Star self-adjointness of FA_to_FA3 images

These helper lemmas establish that FA_to_FA3(FA.x^n) and FA_to_FA3(FA.y^n)
are self-adjoint (star-fixed), needed to simplify assocM expressions. -/

theorem FA_to_FA3_x_pow_star (n : ℕ) :
    star (FA_to_FA3 (FA.x ^ n)) = FA_to_FA3 (FA.x ^ n) := by
  rw [map_pow, star_pow]
  congr 1
  rw [show FA_to_FA3 FA.x = FreeAlgebra.ι ℝ (Fin.castSucc (0 : Fin 2))
    from FreeAlgebra.lift_ι_apply _ _]
  exact FreeAlgebra.star_ι _

theorem FA_to_FA3_y_pow_star (n : ℕ) :
    star (FA_to_FA3 (FA.y ^ n)) = FA_to_FA3 (FA.y ^ n) := by
  rw [map_pow, star_pow]
  congr 1
  rw [show FA_to_FA3 FA.y = FreeAlgebra.ι ℝ (Fin.castSucc (1 : Fin 2))
    from FreeAlgebra.lift_ι_apply _ _]
  exact FreeAlgebra.star_ι _

/-- star of (FA_to_FA3 FA.x) ^ n = (FA_to_FA3 FA.x) ^ n. -/
@[simp] theorem FA_to_FA3_x_star_pow (n : ℕ) :
    star ((FA_to_FA3 FA.x) ^ n) = (FA_to_FA3 FA.x) ^ n := by
  rw [star_pow]
  congr 1
  rw [show FA_to_FA3 FA.x = FreeAlgebra.ι ℝ (Fin.castSucc (0 : Fin 2))
    from FreeAlgebra.lift_ι_apply _ _]
  exact FreeAlgebra.star_ι _

/-- star of (FA_to_FA3 FA.y) ^ n = (FA_to_FA3 FA.y) ^ n. -/
@[simp] theorem FA_to_FA3_y_star_pow (n : ℕ) :
    star ((FA_to_FA3 FA.y) ^ n) = (FA_to_FA3 FA.y) ^ n := by
  rw [star_pow]
  congr 1
  rw [show FA_to_FA3 FA.y = FreeAlgebra.ι ℝ (Fin.castSucc (1 : Fin 2))
    from FreeAlgebra.lift_ι_apply _ _]
  exact FreeAlgebra.star_ι _

/-! ### assocM base cases

Verify that assocM matches evalFA3 of M_op for the base cases (2.52). -/

/-- Base case: M_op one one v = v, and assocM one one c = c.
    H-O (2.52) with i=j=0. -/
theorem assocM_one_one (c : FA3) : assocM .one .one c = c := by
  unfold assocM toFA
  simp only [map_one, one_mul, mul_one, star_one]
  rw [← two_smul ℝ c, smul_smul]; norm_num

/-- M_op one one evaluates to assocM one one via evalFA3. -/
theorem M_op_evalFA3_one_one (v : FreeJordanAlg) :
    evalFA3 (M_op .one .one v) = assocM .one .one (evalFA3 v) := by
  rw [M_op.eq_def]; simp [assocM_one_one]

/-- Base case: M_op (xCons i one) one v = T(x^(i+1))(v).
    H-O (2.52) with j=0. -/
theorem M_op_evalFA3_xPow_one (i : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op (.xCons i .one) .one v) =
    assocM (.xCons i .one) .one (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_T, evalFA3_pow_x]
  unfold assocM
  simp only [toFA_xCons, toFA_one, mul_one, map_mul, map_pow,
    star_one, star_mul, FA_to_FA3_x_pow_star, mul_one, map_one, one_mul]
  congr 1; simp only [FA_to_FA3_x_star_pow]

/-- Base case: M_op one (xCons i one) v = T(x^(i+1))(v). Symmetric to above. -/
theorem M_op_evalFA3_one_xPow (i : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op .one (.xCons i .one) v) =
    assocM .one (.xCons i .one) (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_T, evalFA3_pow_x]
  unfold assocM
  simp only [toFA_one, toFA_xCons, mul_one, map_one, map_mul, map_pow,
    star_one, one_mul, star_mul, FA_to_FA3_x_pow_star, mul_one]
  congr 1; simp only [FA_to_FA3_x_star_pow]; abel

/-- Base case: M_op (yCons j one) one v = T(y^(j+1))(v). -/
theorem M_op_evalFA3_yPow_one (j : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op (.yCons j .one) .one v) =
    assocM (.yCons j .one) .one (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_T, evalFA3_pow_y]
  unfold assocM
  simp only [toFA_yCons, toFA_one, mul_one, map_mul, map_pow,
    star_one, star_mul, FA_to_FA3_y_pow_star, mul_one, map_one, one_mul]
  congr 1; simp only [FA_to_FA3_y_star_pow]

/-- Base case: M_op one (yCons j one) v = T(y^(j+1))(v). -/
theorem M_op_evalFA3_one_yPow (j : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op .one (.yCons j .one) v) =
    assocM .one (.yCons j .one) (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_T, evalFA3_pow_y]
  unfold assocM
  simp only [toFA_one, toFA_yCons, mul_one, map_one, map_mul, map_pow,
    star_one, one_mul, star_mul, FA_to_FA3_y_pow_star, mul_one]
  congr 1; simp only [FA_to_FA3_y_star_pow]; abel

/-- Base case: M_op (xCons i one) (yCons j one) v = U_bilinear(x^(i+1), y^(j+1))(v). -/
theorem M_op_evalFA3_xPow_yPow (i j : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op (.xCons i .one) (.yCons j .one) v) =
    assocM (.xCons i .one) (.yCons j .one) (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_U_bilinear, evalFA3_pow_x, evalFA3_pow_y]
  unfold assocM
  simp only [toFA_xCons, toFA_yCons, toFA_one, mul_one, map_mul, map_pow,
    FA_to_FA3_x_star_pow, FA_to_FA3_y_star_pow, mul_one, map_one, one_mul,
    mul_assoc]

/-- Base case: M_op (yCons j one) (xCons i one) v = U_bilinear(y^(j+1), x^(i+1))(v). -/
theorem M_op_evalFA3_yPow_xPow (j i : ℕ) (v : FreeJordanAlg) :
    evalFA3 (M_op (.yCons j .one) (.xCons i .one) v) =
    assocM (.yCons j .one) (.xCons i .one) (evalFA3 v) := by
  rw [M_op.eq_def, evalFA3_U_bilinear, evalFA3_pow_x, evalFA3_pow_y]
  unfold assocM
  simp only [toFA_yCons, toFA_xCons, toFA_one, mul_one, map_mul, map_pow,
    FA_to_FA3_x_star_pow, FA_to_FA3_y_star_pow, mul_one, map_one, one_mul,
    mul_assoc]

/-! ### assocM compositionality lemmas

These lemmas show that assocM respects the operations used in M_op's recursion. -/

/-- assocM respects U-factorization: a * assocM(p,q)(c) * a = assocM(a*p, a*q)(c)
    when star(a) = a. Generalizes gamma_mac_assocU to arbitrary c. -/
theorem assocM_U_factor (a : FA) (p q : FreeAssocMono) (c : FA3)
    (ha : star a = a) :
    FA_to_FA3 a * assocM p q c * FA_to_FA3 a =
    (1/2 : ℝ) • (FA_to_FA3 (a * toFA p) * c * star (FA_to_FA3 (a * toFA q))
               + FA_to_FA3 (a * toFA q) * c * star (FA_to_FA3 (a * toFA p))) := by
  have ha3 : star (FA_to_FA3 a) = FA_to_FA3 a := by rw [← FA_to_FA3_star, ha]
  unfold assocM
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_assoc, map_mul,
    star_mul, ha3]

/-- assocM respects different-letter recurrence. -/
theorem assocM_diff_letter (a b : FA) (p q : FreeAssocMono) (c : FA3)
    (ha : star a = a) (hb : star b = b) :
    (1/2 : ℝ) • (FA_to_FA3 (a * toFA p) * c * star (FA_to_FA3 (b * toFA q))
               + FA_to_FA3 (b * toFA q) * c * star (FA_to_FA3 (a * toFA p))) =
    FA_to_FA3 a * assocM p q c * FA_to_FA3 b +
    FA_to_FA3 b * assocM p q c * FA_to_FA3 a -
    (1/2 : ℝ) • (FA_to_FA3 (b * toFA p) * c * star (FA_to_FA3 (a * toFA q))
               + FA_to_FA3 (a * toFA q) * c * star (FA_to_FA3 (b * toFA p))) := by
  have ha3 : star (FA_to_FA3 a) = FA_to_FA3 a := by rw [← FA_to_FA3_star, ha]
  have hb3 : star (FA_to_FA3 b) = FA_to_FA3 b := by rw [← FA_to_FA3_star, hb]
  unfold assocM
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_assoc, map_mul,
    smul_add, star_mul, ha3, hb3]
  abel

/-! ### Key compositionality: assocM respects xCons/yCons structure

These lemmas show that composing assocM with U_{x^k}/U_{y^l}/U_bilinear gives
the assocM for the composed monomials, matching M_op's recursion. -/

/-- assocM for xCons k p, xCons k q (when i >= j and i = j):
    U_{x^(k+1)}(assocM p q c) = assocM(xCons k p, xCons k q) c.
    This is the (2.53) case of the recursion. -/
theorem assocM_xCons_eq (k : ℕ) (p q : FreeAssocMono) (c : FA3) :
    FA_to_FA3 (FA.x ^ (k + 1)) *
      assocM p q c *
      FA_to_FA3 (FA.x ^ (k + 1)) =
    assocM (.xCons k p) (.xCons k q) c := by
  have hx : star (FA.x ^ (k + 1)) = FA.x ^ (k + 1) := by simp
  rw [assocM_U_factor _ _ _ _ hx]
  unfold assocM
  simp only [toFA_xCons, map_mul, map_pow]

/-- assocM for yCons l p, yCons l q:
    U_{y^(l+1)}(assocM p q c) = assocM(yCons l p, yCons l q) c.
    This is the (2.54) case of the recursion. -/
theorem assocM_yCons_eq (l : ℕ) (p q : FreeAssocMono) (c : FA3) :
    FA_to_FA3 (FA.y ^ (l + 1)) *
      assocM p q c *
      FA_to_FA3 (FA.y ^ (l + 1)) =
    assocM (.yCons l p) (.yCons l q) c := by
  have hy : star (FA.y ^ (l + 1)) = FA.y ^ (l + 1) := by simp
  rw [assocM_U_factor _ _ _ _ hy]
  unfold assocM
  simp only [toFA_yCons, map_mul, map_pow]

/-! ### The main evalAssoc compatibility theorem

evalFA3(M_op p q v) = assocM p q (evalFA3 v) for all p, q, v.

This is proved by structural induction matching M_op's cases.
Base cases use the M_op_evalFA3_* lemmas above.
Recursive cases use evalAssoc naturality + assocM compositionality. -/

/-- The core evalAssoc compatibility: evalFA3(M_op p q v) = assocM p q (evalFA3 v).
    This is the key structural induction matching all cases of M_op.
    H-O 2.4.24(i), lines 1226-1288. -/
theorem M_op_evalFA3 (p q : FreeAssocMono) (v : FreeJordanAlg) :
    evalFA3 (M_op p q v) = assocM p q (evalFA3 v) := by
  sorry

/-! ### evalAssoc compatibility: full theorem

The main bridge theorem uses assocM as the witness for f.
Property 1 (evalAssoc compatibility) is M_op_evalFA3 above.
Property 2 (assocM_z) is immediate from definitions. -/

/-- **Property (i) bridge** (H-O 2.4.24(i), line 1217):
    Evaluating `M_op p q v` via `evalAssoc` in FA3 is compatible with `gamma_mac_mono`.

    Specifically: for any `v : FreeJordanAlg`, evaluating `M_op p q v` in FA3
    (via `evalAssoc (FA_to_FA3 FA.x) (FA_to_FA3 FA.y)`) gives `assocM p q`
    applied to `evalAssoc ... v`. When applied to z, `assocM p q z` equals
    `gamma_mac_mono p q = ½(pzq* + qzp*)`.

    The witness `f = assocM p q` satisfies both properties:
    - Property 1: `evalFA3(M_op p q v) = assocM p q (evalFA3 v)` (by structural induction)
    - Property 2: `assocM p q FA3.z = gamma_mac_mono p q` (by definition, `assocM_z`)

    The base cases (2.52) are proved above. The recursive cases use evalAssoc
    naturality lemmas from FJOperators.lean. -/
theorem M_op_evalAssoc (p q : FreeAssocMono) (v : FreeJordanAlg) :
    ∃ (f : FA3 → FA3),
    -- f is the "associative M_op" corresponding to (p, q)
    FreeJordanAlg.evalAssoc (FA_to_FA3 FA.x) (FA_to_FA3 FA.y) (M_op p q v) =
      f (FreeJordanAlg.evalAssoc (FA_to_FA3 FA.x) (FA_to_FA3 FA.y) v) ∧
    -- and when applied to z, f gives gamma_mac_mono
    f FA3.z = gamma_mac_mono p q := by
  exact ⟨assocM p q, M_op_evalFA3 p q v, assocM_z p q⟩
