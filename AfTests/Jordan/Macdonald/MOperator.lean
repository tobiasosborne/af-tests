/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FJOperators
import AfTests.Jordan.Macdonald.MonoBlock

/-!
# M_{p,q} Operators (H-O 2.4.24)

Recursive definition of M_{p,q} multiplication operators on FreeJordanAlg,
used in the proof of Macdonald's theorem. The operator M_{p,q} maps
FreeJordanAlg to itself and is defined by induction on w(p) + w(q).

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4.24, (2.52)-(2.57)
-/

open FreeJordanAlg FreeAssocMono

/-- Helper: compose two endomorphisms on FreeJordanAlg. -/
noncomputable def FJComp (f g : FreeJordanAlg → FreeJordanAlg)
    (v : FreeJordanAlg) : FreeJordanAlg :=
  f (g v)

/-- M_{p,q} operator on FreeJordanAlg (H-O 2.4.24).

Defined by induction on `p.weight + q.weight`. Returns a function
`FreeJordanAlg → FreeJordanAlg` representing the multiplication operator. -/
noncomputable def M_op : FreeAssocMono → FreeAssocMono → FreeJordanAlg → FreeJordanAlg
  -- ========================================
  -- (2.52) Base cases: M_{x^i, y^j}
  -- ========================================
  -- M(1, 1) = id
  | .one, .one, v => v
  -- M(x^(i+1), 1) = T_{x^(i+1)}
  | .xCons i .one, .one, v => T (pow x (i + 1)) v
  -- M(1, x^(i+1)) = T_{x^(i+1)}  (by symmetry, U_{1,a} = T_a)
  | .one, .xCons i .one, v => T (pow x (i + 1)) v
  -- M(y^(j+1), 1) = T_{y^(j+1)}
  | .yCons j .one, .one, v => T (pow y (j + 1)) v
  -- M(1, y^(j+1)) = T_{y^(j+1)}
  | .one, .yCons j .one, v => T (pow y (j + 1)) v
  -- M(x^(i+1), y^(j+1)) = U_bilinear(x^(i+1), y^(j+1))
  | .xCons i .one, .yCons j .one, v =>
    U_bilinear (pow x (i + 1)) (pow y (j + 1)) v
  -- M(y^(j+1), x^(i+1)) = U_bilinear(y^(j+1), x^(i+1))
  | .yCons j .one, .xCons i .one, v =>
    U_bilinear (pow y (j + 1)) (pow x (i + 1)) v
  -- ========================================
  -- (2.53) Same letter x: M(xCons i rp, xCons j rq)
  -- where rp, rq ∈ Y
  -- ========================================
  | .xCons i rp, .xCons j rq, v =>
    if h : i ≥ j then
      let reduced := if i = j then rp else xCons (i - j - 1) rp
      U (pow x (j + 1)) (M_op reduced rq v)
    else
      let reduced := if j = i then rq else xCons (j - i - 1) rq
      U (pow x (i + 1)) (M_op rp reduced v)
  -- ========================================
  -- (2.54) Same letter y: M(yCons j rp, yCons k rq)
  -- where rp, rq ∈ X
  -- ========================================
  | .yCons j rp, .yCons k rq, v =>
    if h : j ≥ k then
      let reduced := if j = k then rp else yCons (j - k - 1) rp
      U (pow y (k + 1)) (M_op reduced rq v)
    else
      let reduced := if k = j then rq else yCons (k - j - 1) rq
      U (pow y (j + 1)) (M_op rp reduced v)
  -- ========================================
  -- (2.55) Different letters: M(xCons i rp, yCons j rq)
  -- where rp ∈ Y, rq ∈ X, and not both pure powers (already handled above)
  -- ========================================
  | .xCons i (.yCons k rp'), .yCons j rq, v =>
    (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
        (M_op (.yCons k rp') rq v)
      - M_op (.yCons j (.yCons k rp')) (.xCons i rq) v
  | .xCons i (.xCons l rp'), .yCons j rq, v =>
    -- rp = xCons l rp' starts with x, but rp should be in Y for well-formed.
    -- This case shouldn't arise for WF monomials, but handle it for totality:
    (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
        (M_op (.xCons l rp') rq v)
      - M_op (prependY j (.xCons l rp')) (prependX i rq) v
  -- (2.55b) M(yCons j rq, xCons i rp) — symmetric case
  | .yCons j (.xCons l rq'), .xCons i rp, v =>
    (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
        (M_op (.xCons l rq') rp v)
      - M_op (.xCons i (.xCons l rq')) (.yCons j rp) v
  | .yCons j (.yCons k rq'), .xCons i rp, v =>
    -- rq' starts with y but rq should be in X for WF; handle for totality
    (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
        (M_op (.yCons k rq') rp v)
      - M_op (prependX i (.yCons k rq')) (prependY j rp) v
  -- ========================================
  -- (2.56) Boundary: M(xCons i (yCons k rest'), one)
  -- Weight doesn't decrease naively, so we inline the problematic call
  -- ========================================
  | .xCons i (.yCons k rest'), .one, v =>
    match rest' with
    | .one =>
      -- M(xCons i (yCons k one), one) =
      --   2*T(x^(i+1)) ∘ M(yCons k one, one) - M(yCons k one, xCons i one)
      -- Both recursive calls are base cases (weight ≤ 2)
      (2 : ℝ) • T (pow x (i + 1)) (T (pow y (k + 1)) v)
        - U_bilinear (pow y (k + 1)) (pow x (i + 1)) v
    | .xCons l rest'' =>
      -- M(xCons i (yCons k (xCons l rest'')), one) =
      --   2*T(x^(i+1)) ∘ M(yCons k (xCons l rest''), one)
      --   - M(yCons k (xCons l rest''), xCons i one)
      -- Second call: M(yCons k (xCons l rest''), xCons i one) uses (2.55b)
      -- Both have lower weight after inlining
      (2 : ℝ) • T (pow x (i + 1))
          (M_op (.yCons k (.xCons l rest'')) .one v)
        - M_op (.yCons k (.xCons l rest'')) (.xCons i .one) v
    | .yCons m rest'' =>
      -- rest' = yCons m rest'' — not WF (y after y), handle for totality
      (2 : ℝ) • T (pow x (i + 1))
          (M_op (.yCons k (.yCons m rest'')) .one v)
        - M_op (.yCons k (.yCons m rest'')) (.xCons i .one) v
  -- (2.56b) Symmetric: M(yCons j (xCons l rest'), one)
  | .yCons j (.xCons l rest'), .one, v =>
    match rest' with
    | .one =>
      (2 : ℝ) • T (pow y (j + 1)) (T (pow x (l + 1)) v)
        - U_bilinear (pow x (l + 1)) (pow y (j + 1)) v
    | .yCons m rest'' =>
      (2 : ℝ) • T (pow y (j + 1))
          (M_op (.xCons l (.yCons m rest'')) .one v)
        - M_op (.xCons l (.yCons m rest'')) (.yCons j .one) v
    | .xCons m rest'' =>
      (2 : ℝ) • T (pow y (j + 1))
          (M_op (.xCons l (.xCons m rest'')) .one v)
        - M_op (.xCons l (.xCons m rest'')) (.yCons j .one) v
  -- ========================================
  -- (2.57) Boundary: M(one, yCons j (xCons l rest'))
  -- Symmetric to (2.56) with swapped arguments
  -- ========================================
  | .one, .yCons j (.xCons l rest'), v =>
    match rest' with
    | .one =>
      (2 : ℝ) • T (pow y (j + 1)) (T (pow x (l + 1)) v)
        - U_bilinear (pow x (l + 1)) (pow y (j + 1)) v
    | .yCons m rest'' =>
      (2 : ℝ) • T (pow y (j + 1))
          (M_op .one (.xCons l (.yCons m rest'')) v)
        - M_op (.yCons j .one) (.xCons l (.yCons m rest'')) v
    | .xCons m rest'' =>
      (2 : ℝ) • T (pow y (j + 1))
          (M_op .one (.xCons l (.xCons m rest'')) v)
        - M_op (.yCons j .one) (.xCons l (.xCons m rest'')) v
  -- (2.57b) M(one, xCons i (yCons k rest'))
  | .one, .xCons i (.yCons k rest'), v =>
    match rest' with
    | .one =>
      (2 : ℝ) • T (pow x (i + 1)) (T (pow y (k + 1)) v)
        - U_bilinear (pow y (k + 1)) (pow x (i + 1)) v
    | .xCons l rest'' =>
      (2 : ℝ) • T (pow x (i + 1))
          (M_op .one (.yCons k (.xCons l rest'')) v)
        - M_op (.xCons i .one) (.yCons k (.xCons l rest'')) v
    | .yCons m rest'' =>
      (2 : ℝ) • T (pow x (i + 1))
          (M_op .one (.yCons k (.yCons m rest'')) v)
        - M_op (.xCons i .one) (.yCons k (.yCons m rest'')) v
  -- ========================================
  -- Remaining: M(one, xCons i (xCons ...)) and M(one, yCons j (yCons ...))
  -- These are non-WF (same letter consecutive), handle for totality
  -- ========================================
  | .one, .xCons i (.xCons l rest'), v =>
    T (pow x (i + 1)) (M_op .one (.xCons l rest') v)
  | .one, .yCons j (.yCons k rest'), v =>
    T (pow y (j + 1)) (M_op .one (.yCons k rest') v)
  -- M(xCons i (xCons ...), one) — non-WF
  | .xCons i (.xCons l rest'), .one, v =>
    T (pow x (i + 1)) (M_op (.xCons l rest') .one v)
  -- M(yCons j (yCons ...), one) — non-WF
  | .yCons j (.yCons k rest'), .one, v =>
    T (pow y (j + 1)) (M_op (.yCons k rest') .one v)
  -- ========================================
  -- (2.55) Pure power vs long monomial (different letters)
  -- ========================================
  -- M(xCons i one, yCons j (xCons l rest'))
  | .xCons i .one, .yCons j (.xCons l rest'), v =>
    (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
        (M_op .one (.xCons l rest') v)
      - M_op (prependY j .one) (prependX i (.xCons l rest')) v
  -- M(xCons i one, yCons j (yCons k rest'))
  | .xCons i .one, .yCons j (.yCons k rest'), v =>
    (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
        (M_op .one (.yCons k rest') v)
      - M_op (prependY j .one) (prependX i (.yCons k rest')) v
  -- M(yCons j one, xCons i (yCons k rest'))
  | .yCons j .one, .xCons i (.yCons k rest'), v =>
    (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
        (M_op .one (.yCons k rest') v)
      - M_op (prependX i .one) (prependY j (.yCons k rest')) v
  -- M(yCons j one, xCons i (xCons l rest'))
  | .yCons j .one, .xCons i (.xCons l rest'), v =>
    (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
        (M_op .one (.xCons l rest') v)
      - M_op (prependX i .one) (prependY j (.xCons l rest')) v
termination_by p q _ => p.weight + q.weight
decreasing_by all_goals sorry
