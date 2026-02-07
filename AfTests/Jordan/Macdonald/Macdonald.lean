/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.MOperatorProperties
import AfTests.Jordan.Macdonald.TensorSetup
import AfTests.Jordan.Macdonald.GammaInjectivity
import AfTests.Jordan.Macdonald.GeneratorLemma
import AfTests.Jordan.Macdonald.MonomialFJ

/-!
# Macdonald's Theorem (H-O 2.4.13, 2.4.25)

Statement and proof skeleton for Macdonald's theorem: the canonical map
`evalFA : FreeJordanAlg → FA` is injective, i.e., the free Jordan algebra
on 2 generators is special (isomorphic to a subalgebra of an associative algebra).

## Main results

* `M_op_eval_z` — Property (i): M_{p,q}(z) = gamma_mac(p,q) in FA3
* `mult_alg_surjectivity` — Part A: every T_v is in the ℝ-span of M_{p,q} operators
* `gamma_mac_injective` — Part B: gamma_mac is injective on symmetric tensors
* `macdonald` — If evalFA(v) = 0 then v = 0
* `macdonald_injectivity` — evalFA is injective
* `fundamental_formula_free` — FF holds in FreeJordanAlg
* `fundamental_formula_general` — FF holds in every JordanAlgebra

## Proof outline (H-O 2.4.25)

**Part A (Surjectivity):** Every T_v lies in the ℝ-linear span of {M_{p,q}}.
- M_{1,1} = id (property ii, `M_op_one_one`)
- Closed under U_{x^k} (property iii, `M_op_xCons_xCons`/`M_op_yCons_yCons`)
- Closed under U_{x^k,y^l} (property iv, `M_op_U_bilinear_yCons`/`M_op_U_bilinear_xCons`)
- By GeneratorLemma, {U_{a,b} : a,b in {1,x,y}} generate the multiplication algebra

**Part B (Injectivity):** `gamma_mac` is injective on symmetric tensors (Step 15).
Monomials `pzq*` in FA3 with exactly one z uniquely determine p and q.

**Conclusion:** If evalFA(v) = 0, then M_v acts as zero on all special JAs.
By property (i), M_v(z) = gamma_mac(v) = 0 in FA3. By injectivity, v = 0.

## References

* Hanche-Olsen & Stormer, "Jordan Operator Algebras", Section 2.4
-/

open FreeJordanAlg FreeAssocMono

/-! ### Property (i): M_{p,q}(z) = gamma_mac evaluated in FA3

This connects M_op (which acts on FreeJordanAlg) to gamma_mac (which maps
symmetric tensors to FA3). Proof is by induction on weight, using the
recursive structure of M_op and properties (ii)-(iv). -/

/-- Property (i): M_{p,q} applied to a "generic" third variable z gives
    gamma_mac(p,q) = ½(pzq* + qzp*) in FA3.

    More precisely: for any p, q : FreeAssocMono, evaluating M_op p q on
    the generator z of a 3-variable algebra yields gamma_mac(p_FA, q_FA)
    where p_FA, q_FA are the images of p, q in FA. -/
/- The real statement of property (i) requires:
   - `toFA : FreeAssocMono → FA` converting monomials to free algebra elements
   - An evaluation of FreeJordanAlg into FA3 (the 3-generator free algebra)
   These are not yet defined. The statement would be:
     `evalAssoc3 (FA_to_FA3 FA.x) (FA_to_FA3 FA.y) FA3.z (M_op p q z_FJ) =
      gamma_mac (toFA p) (toFA q)`
   where `z_FJ` is the generator z viewed in FreeJordanAlg on 3 generators
   and `evalAssoc3` evaluates into the 3-generator associative algebra. -/
theorem M_op_eval_z_placeholder : True := trivial

/-! ### Part A: Surjectivity of t ↦ M_t

Every multiplication operator T_v on FreeJordanAlg lies in the ℝ-linear span
of the M_{p,q} operators. The key ingredients:
- M_{1,1} = id (property ii)
- Closure under U_{x^k} (property iii)
- Closure under U_{x^k,y^l} (property iv)
- Generator lemma: {U_{a,b} : a,b in {1,x,y}} generate the multiplication algebra -/

/-- Every multiplication operator T_v on FreeJordanAlg lies in the ℝ-linear span
    of the M_{p,q} operators: for every v : FreeJordanAlg, T_v can be expressed
    as a finite ℝ-linear combination of M_{p,q} operators.

    This is Part A of the Macdonald theorem proof (H-O 2.4.25).

    **Note:** An earlier version stated `∃ (p q), ∀ w, M_op p q w = T v w`,
    which is mathematically false — a single M_{p,q} cannot in general express
    T_v. The correct statement is that T_v is a *finite linear combination* of
    such operators, proved by induction on v using the generator lemma and
    closure properties (ii)–(iv). -/
theorem mult_alg_surjectivity (v : FreeJordanAlg) :
    ∃ (c : FreeAssocMono × FreeAssocMono →₀ ℝ),
    ∀ w, FreeJordanAlg.T v w = c.sum (fun pq r => r • M_op pq.1 pq.2 w) := by
  sorry

/-! ### Part B: Gamma injectivity (Step 15)

gamma_mac is injective on symmetric tensors. The full proof needs
the basis structure of FreeAlgebra, so it is done in a separate file.
Here we state the result needed for the conclusion. -/

/-- gamma_mac is injective: if gamma_mac(p,q) = 0 for all corresponding
    symmetric tensor elements, then the tensor is zero.

    The proof uses the fact that monomials `pzq*` in FA3 with exactly one z
    uniquely determine p and q (z acts as a separator). -/
theorem gamma_mac_injective :
    ∀ (a b : FA), gamma_mac a b = 0 → gamma_mac b a = 0 →
    a ⊗ₜ[ℝ] b + b ⊗ₜ[ℝ] a = (0 : FA2) := by
  intro a b hab hba
  -- Let t = a ⊗ b + b ⊗ a. We show t ∈ symTensor and gamma_mac_tensor t = 0.
  set t := a ⊗ₜ[ℝ] b + b ⊗ₜ[ℝ] a with ht_def
  -- Step 1: t ∈ symTensor (comm swaps factors, then add_comm gives t back)
  have ht_sym : t ∈ symTensor := by
    change LinearMap.id t = (TensorProduct.comm ℝ FA FA).toLinearMap t
    simp [t, map_add, TensorProduct.comm_tmul]
    abel
  -- Step 2: gamma_mac_tensor t = 0
  have ht_zero : gamma_mac_tensor t = 0 := by
    simp [t, map_add, gamma_mac_tensor_tmul, hab, hba]
  -- Step 3: Apply injectivity on symTensor
  have h0_sym : (0 : FA2) ∈ symTensor := Submodule.zero_mem _
  have heq : gamma_mac_tensor.domRestrict symTensor ⟨t, ht_sym⟩ =
             gamma_mac_tensor.domRestrict symTensor ⟨0, h0_sym⟩ := by
    simp [LinearMap.domRestrict_apply, ht_zero]
  exact Subtype.mk.inj (gamma_mac_injective_symTensor heq)

/-! ### Macdonald's theorem -/

/-- **Macdonald's theorem** (H-O 2.4.13): If v ∈ FreeJordanAlg satisfies
    evalFA(v) = 0 (i.e., v evaluates to 0 in the free associative algebra
    FA = FreeAlgebra ℝ (Fin 2)), then v = 0.

    Equivalently: the free Jordan algebra on 2 generators is special.

    **Proof sketch** (H-O 2.4.25):
    1. (Part A) Every multiplication operator T_v on FJ{x,y} lies in the
       ℝ-linear span of {M_{p,q}}, by `mult_alg_surjectivity`.
    2. (Property i) M_t applied to a test element z gives gamma_mac(t) in FA3.
    3. If evalFA(v) = 0, then v acts as zero in all special Jordan algebras.
       In particular M_v(z) = gamma_mac(v) = 0 in FA3.
    4. (Part B) gamma_mac is injective on symmetric tensors, so t = 0, hence v = 0. -/
theorem macdonald (v : FreeJordanAlg) (h : evalFA v = 0) : v = 0 := by
  sorry

/-- Macdonald's theorem, injectivity form: `evalFA` is injective. -/
theorem macdonald_injectivity : Function.Injective evalFA := by
  intro u v huv
  -- Show u = v by showing evalFA(u - v) = 0, then applying macdonald
  suffices h : u - v = 0 from sub_eq_zero.mp h
  apply macdonald
  -- evalFA(u - v) = evalFA(u) - evalFA(v) = 0
  have : u - v = u + (-1 : ℝ) • v := by simp [sub_eq_add_neg]
  rw [this, evalFA_add, evalFA_smul, huv, neg_one_smul, add_neg_cancel]

/-! ### Fundamental formula via Macdonald -/

/-- The fundamental formula holds in FreeJordanAlg:
    U_{U_x(y)}(w) = U_x(U_y(U_x(w))) for all w.

    This follows from `special_fundamental_formula` (which proves it in every
    associative algebra) combined with `macdonald_injectivity` (which says that
    if two FreeJordanAlg elements agree in FA, they are equal). -/
theorem fundamental_formula_free (u v w : FreeJordanAlg) :
    FreeJordanAlg.U (FreeJordanAlg.U u v) w =
    FreeJordanAlg.U u (FreeJordanAlg.U v (FreeJordanAlg.U u w)) := by
  -- By macdonald_injectivity, it suffices to show evalFA of both sides agree
  apply macdonald_injectivity
  -- Both sides evaluate to the same thing in FA by special_fundamental_formula
  exact special_fundamental_formula FA.x FA.y u v w

/-! ### Transfer to general Jordan algebras -/

/-- The fundamental formula holds in every Jordan algebra:
    U_{U_a(b)}(x) = U_a(U_b(U_a(x))) for all a, b, x in J.

    **Status**: sorry — requires one of:

    1. **Generalize FreeJordanAlg to n generators** (recommended).
       Currently `FreeJordanAlg` has exactly 2 generators (x, y). The evaluation
       map `evalJA : FreeJordanAlg → J` with x↦a, y↦b only reaches the
       subalgebra ⟨a,b⟩ ⊆ J. Since `fundamental_formula_free` proves FF for
       all w ∈ FJ{x,y}, the transfer via evalJA gives FF only for
       x ∈ im(evalJA) = ⟨a,b⟩, NOT for arbitrary x ∈ J.
       With FreeJordanAlg on 3+ generators, we could substitute z↦x and
       get FF for all x ∈ J by the universal property.

    2. **Macdonald's theorem** (H-O 2.4.13, 2.4.15) applied as a metatheorem.
       The FF is an operator identity F(a,b) = 0 where both sides are linear
       in the "test variable" x. Macdonald says: a polynomial identity in 2
       variables, linear in a 3rd, that holds in all special JAs, holds in all
       JAs. This is the approach of H-O 2.4.18. But formalizing the
       metatheoretic transfer requires `macdonald` (which itself has a sorry).

    3. **Direct algebraic proof** from Jordan axioms (McCrimmon's approach).
       Lengthy (~100 LOC) but avoids Macdonald entirely. Uses iterated
       linearization of the Jordan identity and operator composition formulas.

    See also: `JordanAlgebra.fundamental_formula` in FundamentalFormula.lean,
    which has the same sorry for the same reason. -/
theorem fundamental_formula_general {J : Type*} [JordanAlgebra J]
    (a b x : J) :
    JordanAlgebra.U (JordanAlgebra.U a b) x =
    JordanAlgebra.U a (JordanAlgebra.U b (JordanAlgebra.U a x)) := by
  sorry
