# Handoff: 2026-02-04 (Session 70)

## Completed This Session

### L_jpow_comm_all l=2 case COMPLETE (LinearizedJordan.lean:340-452)

Filled the `l=2, m=k+2` sorry in `L_jpow_comm_all`. Key structural fix:
added `revert m` before outer strong induction so `ih` has type
`∀ l' < l, ∀ m, Commute ...` (not fixed to one `m`). This lets the inner
strong induction on `m` access the outer IH at different `m` values.

Status of `L_jpow_comm_all`:
- **l=0**: proved
- **l=1**: proved
- **l=2**: PROVED (all m, via nested strong induction + operator_formula)
- **l=n+3**: **sorry** (one remaining sorry)

### l=n+3 sorry (LinearizedJordan.lean:453)

**Exact same pattern** as l=2 case and as L_jpow_comm_L's n+3 case:
1. Get IH: `ih 1 m`, `ih 2 m`, `ih (n+1) m`, `ih (n+2) m` (all < n+3)
2. Convert to element-level commutativity (hc1..hc4)
3. `operator_formula_apply a a (jpow a (n+1)) x` → `expr_x`
4. Same with `(jmul (jpow a m) x)` → `expr_mx`
5. Calc chain: substitute term-by-term using hc1..hc4
~40 LOC, mechanical copy of l=2 pattern.

---

## Previous Session (68)

### Closed af-gk4c: jpow_add already proved (LinearizedJordan.lean:340-383)

`jpow_add` (power associativity, H-O 2.4.4) and `jpow_assoc` were already fully proved
in LinearizedJordan.lean. Also `L_jpow_comm_L` (Commute (L a) (L (jpow a n))) at :200-336.
Issue was created in session 67 but the theorem predates it. Closed as already done.

### Identified key blocker for H-O 2.4.21 power formulas

To prove (2.45) `2T_{a^l} U_{a^m,a^n} = U_{a^{m+l},a^n} + U_{a^m,a^{n+l}}`, need:
1. **L_jpow_comm_all** (af-jify, P1): `Commute (L (jpow a l)) (L (jpow a m))` for all l, m
   - Currently only have `L_jpow_comm_L`: Commute (L a) (L (jpow a n))
   - H-O 2.4.5(ii) states all T_{a^n} mutually commute
2. **power_triple_comm**: `triple (a^m) (a^l ∘ x) (a^n) = a^l ∘ triple (a^m) x (a^n)`
3. **power_triple_formula** (2.45): follows from triple_product_242 + above two

**Proof strategy for L_jpow_comm_all** (af-jify):
- Strong induction on l
- l=0: trivial, l=1: L_jpow_comm_L, l=2: induction on m via operator_formula
- l=n+3: operator_formula recursion gives L_{a^{n+3}} = 2 L_a L_{a^{n+2}} + L_{a^{n+1}}(L_{a²} - 2L_a²)
  All subterms commute with L_{a^m} by IH + L_jpow_comm_L
- File: LinearizedJordan.lean after L_jpow_comm_L, ~50-80 LOC

---

## Previous Session (66)

### triple_product_243 and triple_product_244 PROVED (FundamentalFormula.lean:112-139, no sorry)

Added the remaining two identities from H-O 2.4.20:

**Identity (2.43)** — `triple_product_243`:
```lean
theorem triple_product_243 (a b c d : J) :
    jmul (triple a b c) d =
    triple a (jmul b c) d - triple (jmul a c) b d + triple c (jmul a b) d
```
Proof (~10 LOC): One instance of `four_variable_identity(a,b,c,d)` plus `jmul_comm` normalization.
The goal difference equals `-(fvi_LHS - fvi_RHS)`, closed by `neg_zero`.

**Identity (2.44)** — `triple_product_244`:
```lean
theorem triple_product_244 (a b c d : J) :
    jmul (triple a b c) d + jmul (triple d b c) a =
    triple a (jmul b c) d + triple (jmul a d) b c
```
Proof (~4 LOC): Derived from (2.43) for the first term + (2.42) for the second (with a↔d),
then `triple_comm_outer` cancellations + `abel`.

All three H-O 2.4.20 identities are now complete: (2.42), (2.43), (2.44).

---

## Previous Session (65)

Filled the sorry in `triple_product_242` (H-O 2.4.20, identity 2.42):
```lean
theorem triple_product_242 (a b c d : J) :
    jmul (triple a b c) d =
    triple (jmul a d) b c + triple a b (jmul c d) - triple a (jmul b d) c
```

**Proof technique** (~20 LOC):
1. Expand triples: `simp only [triple_def, add_jmul, sub_jmul]`
2. Introduce h1/h2/h3 = `four_variable_identity` with args `(d,a,b,c)`, `(d,b,c,a)`, `(d,a,c,b)`
3. Normalize d-commutativity: `simp only [jmul_comm d] at h1 h2 h3`
4. Normalize remaining commutativity via targeted `rw [jmul_comm ...] at h2/h3`
5. Convert to zero-form: `sub_eq_zero.mpr h1/h2/h3`
6. Close via `calc` with `abel` + `rw [e1, e2, e3]; abel`

**Key insight**: `linear_combination` requires `CommSemiring` (unavailable for non-associative
Jordan algebras). Workaround: express `goal_diff` as `(h1_diff)+(h2_diff)-(h3_diff)` via `abel`,
then substitute each diff = 0.

---

## Previous Session (64)

### Verified triple_product_242 proof approach against H-O 2.4.20 (no code changes)

**Manual verification** that the proposed proof strategy for `triple_product_242` correctly
follows Hanche-Olsen & Størmer §2.4.20. Checked by expanding all 12 terms of the goal
and all 18 terms of h1+h2-h3 and confirming exact term-by-term match (modulo `jmul_comm`).

**H-O 2.4.20 proof structure:**
1. Expand all four triple products in (2.42)
2. Sum equals `(abcd) - (a;bcd) + (b;acd) - (c;abd)`
3. Each `(x;yzw) = (xyzw)` by `four_variable_identity`, and `(xyzw)` is fully symmetric
4. So sum = `(abcd) - (abcd) + (abcd) - (abcd) = 0`

**HANDOFF approach maps to H-O as follows:**
- h1 = `fvi(d,a,b,c)` corresponds to `(d;abc) = (abcd)`
- h2 = `fvi(d,b,c,a)` corresponds to `(d;bca) = (abcd)`
- h3 = `fvi(d,a,c,b)` corresponds to `(d;acb) = (abcd)`
- `h1 + h2 - h3` gives exactly the 12-term goal difference — **verified term by term**

**Conclusion:** The approach is correct. No hallucination. Next session should implement
the ~15 `jmul_comm` rewrites + `linarith [h1, h2, h3]` or `linear_combination h1 + h2 - h3`.

---

## Previous Session (63)

### Triple product identity (2.42) statement added (FundamentalFormula.lean:84-91)

Added theorem statement for H-O 2.4.20, identity (2.42):
```lean
theorem triple_product_242 (a b c d : J) :
    jmul (triple a b c) d =
    triple (jmul a d) b c + triple a b (jmul c d) - triple a (jmul b d) c
```

**Proof strategy (verified correct in Session 64, ready to implement):**

1. `simp only [triple_def, add_jmul, sub_jmul]` — expands to 3 LHS atoms, 9 RHS atoms
2. Introduce `h1 := four_variable_identity d a b c`, `h2 := four_variable_identity d b c a`,
   `h3 := four_variable_identity d a c b`
3. After depth-1 normalization (`simp only [jmul_comm d a, jmul_comm d c]` etc.):
   - h1 gives: G1 + G11 + G6 = G7 + G12 + G5
   - h2 gives: G2 + G9 + G10 = G5 + G7 + G12
   - h3 gives: G3 + G8 + G4 = G12 + G7 + G5
4. Goal = h1 + h2 - h3 (rearranged), closeable by `abel`
5. **Key difficulty**: ~15 `jmul_comm` rewrites needed to normalize atoms in h1/h2/h3
   to match goal atoms. Inner depth-1 commutativity (`jmul d a → jmul a d`) is easy,
   but outer commutativity on compound terms (`jmul (jmul b c) a → jmul a (jmul b c)`,
   `jmul d (jmul (jmul a b) c) → jmul (jmul (jmul a b) c) d`) requires specific instances.
6. After normalization, need to derive `G1 = ... from h1'` etc. in AddCommGroup
   (no `linarith`, need manual `calc` + `abel` or similar).

**Atoms mapping** (G = goal atom):
- G1=`(ab)c∘d`, G2=`a(bc)∘d`, G3=`b(ac)∘d` (LHS, G3 negative)
- G4=`((ad)b)c`, G5=`(ad)(bc)`, G6=`b((ad)c)` (triple(ad,b,c), G6 negative)
- G7=`(ab)(cd)`, G8=`a(b(cd))`, G9=`b(a(cd))` (triple(a,b,cd), G9 negative)
- G10=`(a(bd))c`, G11=`a((bd)c)`, G12=`(bd)(ac)` (triple(a,bd,c), G10/G11 negative, G12 positive)

**Identities (2.43) and (2.44)** still need statements added. Same proof pattern.

---

## Previous Session (62)

### Course correction: JTPI approach abandoned, H-O path identified

The "JTPI" (`{a, U_a(b), x} = U_a({a,b,x})`) as intermediate step to the fundamental
formula is NOT from Hanche-Olsen. It was a hallucinated approach. H-O's actual path:

1. **H-O 2.4.18**: The fundamental formula `U_{U_a(b)} = U_a U_b U_a` follows from
   **Macdonald's theorem** (2.4.13/2.4.15). It's trivially true in associative algebras
   and Macdonald says 3-variable polynomial identities true in special ⇒ true in all.

2. **H-O 2.4.20**: The identities H-O DOES prove directly (from four_variable_identity):
   - (2.42): `{abc} ∘ d = {(a∘d)bc} + {ab(c∘d)} - {a(b∘d)c}`
   - (2.43): `{abc} ∘ d = {a(b∘c)d} - {(a∘c)bd} + {c(a∘b)d}`
   - (2.44): `{abc} ∘ d + {dbc} ∘ a = {a(b∘c)d} + {(a∘d)bc}`

3. **H-O 2.4.21**: Power formulas (2.45)-(2.46) follow from (2.42) + power associativity.

**Correct next steps** (new issues created with dependencies):
- `af-9qp2` (P1): Prove (2.42)-(2.44) from four_variable_identity
- `af-u0tp` (P2): Prove (2.45)-(2.46) power formulas
- `af-tggl` (P3): Formalize Macdonald's theorem (major effort, ~200+ LOC)

The `jtpi` sorry at FundamentalFormula.lean:79 should be **removed** — it's not an
intermediate step in H-O's proof. The fundamental formula sorry should reference
Macdonald's theorem directly.

---

## Previous Session (61)

### JTPI proof analysis — deep algebraic computation documented

Investigated the JTPI sorry at `FundamentalFormula.lean:79`. Key findings:

**After expansion** (`simp only [triple_def, U_def, two_smul, jmul_sub, jmul_add, sub_jmul, add_jmul]`),
the goal becomes matching 12 distinct depth-4 jmul atoms (6 per side, no overlap).

**Available identities** (all proven in LinearizedJordan.lean, OperatorIdentities.lean):
- `operator_formula_apply(a,a,ab,x)`: relates atoms (1),(3),(7) + extra `(ab)(a²x)`, `(ab)(a(ax))`
- `four_variable_identity(a,a,ab,x)`: gives `2(3) + (ab)(a²x) = 2(5) + (10)`
- `operator_commutator_jsq_apply`: converts a²-commutator into L_a compositions
- `fundamental_jordan'`: swaps a and a² in adjacent positions

**Key difficulty**: All identities introduce "extra atoms" (e.g., `(ab)(a²x)`, `a((ab)(ax))`).
When extra atoms are eliminated using other identities, the remaining relations among atoms 1-12
are tautological. This means the current identity set is INSUFFICIENT to derive JTPI by
simple linear combination + abel.

**Why brute force fails**: No Lean tactic handles non-associative algebra equalities.
`ring` requires associativity, `abel` only handles the additive group, and `linear_combination`
requires `ring` as normalizer. A custom non-associative rewrite tactic would be needed.

**Recommended approaches for next session**:
1. **Operator-level proof**: Work at `LinearMap` level using `ext`, prove
   `V_{a, U_a(b)} = U_a ∘ V_{a,b}` as operator equation using `operator_formula`,
   `operator_commutator_jsq`, and `L_comm_L_sq`. More structured than element-level.
2. **Verify for matrices first**: Prove JTPI for `RealSymmetricMatrix` where it reduces
   to associative algebra: `{a, aba, x} = a(a({a,b,x})b)a` by `ring`. This gives confidence
   and a concrete instance.
3. **Shirshov-Cohn approach**: JTPI involves only 2 generators (a,b with x free/linear).
   Shirshov-Cohn says 2-generated Jordan ⇒ special. Verify in special algebras, conclude generally.
   Major formalization effort but reusable for FF and other identities.

---

## Previous Session (60)

### JTPI + proof structure for fundamental formula (FundamentalFormula.lean, ~25 LOC)

Added JTPI and jtpi_outer as sorry'd lemmas, improved documentation:

**FundamentalFormula.lean**:
1. `jtpi` (sorry) — JTPI: {a, U_a(b), x} = U_a({a, b, x})
2. `jtpi_outer` — {x, U_a(b), a} = U_a({x, b, a}) (from jtpi + triple_comm_outer)
3. Improved `fundamental_formula` documentation with proof approach options

**Key discovery**: Standard proofs of FF use Shirshov-Cohn theorem (any 2-generated
Jordan algebra is special) or Macdonald's principle — NOT a direct derivation from
JTPI. A direct element-level proof of JTPI requires ~12-term manipulation using
Jordan identity + operator_commutator_jsq. Attempted proof sketch uses:
- Expand via `simp only [triple_def, U_def, jsq_def]`
- Distribute with `jmul_sub, jmul_add, smul_jmul` etc.
- Apply Jordan identity `j1` and `operator_commutator_jsq_apply`
- Close with `abel`

---

## Previous Session (59)

### V-L commutator identity (OperatorIdentities.lean + FundamentalFormula.lean, ~32 LOC)

Four new lemmas toward the fundamental formula:

**OperatorIdentities.lean** (helpers):
1. `opComm_add_left` — ⟦f+g, h⟧ = ⟦f,h⟧ + ⟦g,h⟧
2. `opComm_add_right` — ⟦f, g+h⟧ = ⟦f,g⟧ + ⟦f,h⟧
3. `opComm_neg_right` — ⟦f, -g⟧ = -⟦f,g⟧

**FundamentalFormula.lean** (key theorem):
4. `V_opComm_L` — ⟦V_{a,b}, L_c⟧ = ⟦L_a, V_{b,c}⟧ + ⟦L_b, V_{c,a}⟧

**Proof technique for V_opComm_L:**
- Expand V via `V_eq_L_add_opComm`, distribute with `opComm_add_left/right`
- Apply Jacobi + skew + neg_right to simplify double commutators
- Remaining equality is `opComm_L_sum` (with `jmul_comm`)
- Close with `rw [← h]; abel`

---

## Previous Session (57)

### Jordan triple product and V operator (Quadratic.lean, FundamentalFormula.lean)

Added infrastructure for the fundamental formula proof:

**Quadratic.lean** (~40 LOC added):
- `triple a b c` — Jordan triple product {a,b,c} = (a∘b)∘c + a∘(b∘c) - b∘(a∘c)
- `triple_self_right : triple a b a = U a b` — recovers U operator
- `triple_comm_outer : triple a b c = triple c b a` — outer symmetry
- `V_linear a b : J →ₗ[ℝ] J` — V operator as linear map, V_{a,b}(x) = {a,b,x}
- `V_self : V_linear a a x = jmul (jsq a) x` — self-V is L_{a²}

**FundamentalFormula.lean** (~12 LOC added):
- `V_eq_L_add_opComm : V_linear a b = L (jmul a b) + ⟦L a, L b⟧` — operator form
- `V_add_V_swap : V_{a,b}(x) + V_{b,a}(x) = 2(ab)x` — symmetrization

### Closed stale issues
- `af-8anj`: csoi_refine_primitive (proved session 55)
- `af-hbnj`: exists_primitive_decomp (proved session 53)

---

## Previous Session (56)

### Removed false operator identities (OperatorIdentities.lean)

Verified on 2×2 symmetric matrices that `opComm_double_idempotent` and `L_e_L_a_L_e`
are **FALSE**. Counterexample: e=diag(1,0), a=[[0,1],[1,0]], x=[[1,0],[0,0]] gives
LHS=[[0,1/8],[1/8,0]] vs RHS=[[0,1/4],[1/4,0]].

Removed both sorry'd theorems from `OperatorIdentities.lean`. Build passes.
Closed `af-cnnp` (P0) and `af-j60a` (P0).

---

## Previous Session (55)

### csoi_refine_primitive COMPLETE (Primitive.lean:1546-1587)

**Proved** `csoi_refine_primitive`: a CSOI with nonzero idempotents can be refined to a
primitive CSOI with at least as many elements. ~35 LOC, no sorry.

**Proof strategy**:
1. Decompose each `c.idem i` into primitives via `exists_primitive_decomp` (`choose`)
2. Combine families using `finSigmaFinEquiv` (sigma-to-Fin equivalence)
3. Same-group orthogonality: `ho i` (internal pairwise orthogonality)
4. Cross-group orthogonality: `sub_idem_orthog_of_sum_orthog` + `primitive_sum_sub_idem`
5. Completeness: `Fintype.sum_equiv` + `Finset.sum_sigma` + `c.complete`
6. Count: each `k i ≥ 1` (nonzero idempotent), so `∑ k i ≥ n`

**Key technique**: `rcases h : finSigmaFinEquiv.symm j with ⟨i, l⟩` to destructure
sigma pairs while retaining the equation for later rewrites.

---

## Previous Session (54)

### exists_primitive_csoi (Primitive.lean:1536-1540)

**Proved** `exists_primitive_csoi`: a primitive CSOI exists in any nontrivial finite-dimensional
formally real Jordan algebra. ~3 LOC, no sorry. Applies `exists_primitive_decomp` to `jone`.

### Repaired exists_primitive_decomp (Primitive.lean:1464-1533)

Fixed 4 pre-existing compilation errors from mathlib API changes:
- `rw [hd]` → `rw [← hd]` (rewrite direction)
- `rfl` → `he_eq` (explicit equation for `sub_idem_finrank_lt`)
- Delayed `intro hij` until after `Fin.addCases` case split (motive substitution fix)

### Corrected csoi_refine_primitive signature (Primitive.lean:1542-1548)

Added `(h_ne : ∀ i, c.idem i ≠ 0)` hypothesis — the original `m ≥ n` claim is unprovable
without it (zero idempotents are valid in a CSOI).

---

## Previous Session (53)

### exists_primitive_decomp COMPLETE (Primitive.lean:1464-1533)

**Proved** `exists_primitive_decomp`: every nonzero idempotent decomposes into a sum of
pairwise orthogonal primitives. ~55 LOC, no sorry.

**Proof strategy** (strong induction on finrank P₁(e)):

1. **Base case**: If e is already primitive, return singleton family `![e]`
2. **Inductive case**: e not primitive → extract sub-idempotent f (via push_neg on IsPrimitive)
   - Set g = e - f (idempotent by `sub_idempotent_of_jmul_eq`)
   - f ⊥ g (by `orthogonal_of_jmul_eq`)
   - finrank P₁(f) < finrank P₁(e) and finrank P₁(g) < finrank P₁(e) (by `sub_idem_finrank_lt`)
   - Recurse on f and g, combine with `Fin.addCases`
   - Cross-orthogonality: `sub_idem_orthog_of_sum_orthog` + `primitive_sum_sub_idem`
   - Sum: `Fin.sum_univ_add` + `Fin.addCases_left/right`

**Key pattern**: `Fin.addCases` for combining Fin-indexed families (same as `OrderedCone.lean`).

---

## Previous Session (52)

### Helper Lemmas for exists_primitive_decomp (Primitive.lean:1438-1462)

Added the two remaining helper lemmas needed for `exists_primitive_decomp`.

**Proof structure** (strong induction on finrank P₁(e)):

1. **Base case** (finrank = 1): e is primitive by `isPrimitive_of_peirce_one_dim_one`
   - Return `![e]`

2. **Inductive case** (finrank > 1): e not primitive
   - Extract f with `IsIdempotent f`, `jmul e f = f`, `f ≠ 0`, `f ≠ e`
   - Set `g = e - f` (idempotent by `sub_idempotent_of_jmul_eq`)
   - f ⊥ g by `orthogonal_of_jmul_eq`
   - Recurse on f and g (finrank decreases by `sub_idem_finrank_lt`)
   - Combine with `Fin.append`

**Key syntax notes**:
- Use `| _ n ih =>` not `| ind n ih =>` for `Nat.strong_induction_on`
- Use `Nat.lt_or_eq_of_le` or `le_iff_lt_or_eq` not `Nat.eq_or_gt_of_le`

---

## Previous Session (50)

### New Helper Lemmas (Primitive.lean:1372-1393)

Added key lemmas for combining orthogonal decompositions:

1. **sub_idem_orthog_of_orthog**: If f ⊥ g and p is a sub-idempotent of f (jmul f p = p), then p ⊥ g
   - Uses: orthogonal_in_peirce_zero, peirce_mult_P0_P1

2. **sub_idem_orthog_of_sum_orthog**: If f ⊥ g, p₁ ≤ f, p₂ ≤ g, then p₁ ⊥ p₂
   - Key for combining primitive decompositions of orthogonal idempotents

---

## Previous Session (49)

### Helper Lemmas for exists_primitive_decomp (Primitive.lean:1367-1412)

Added key lemmas enabling induction on finrank P₁(e):

1. **sub_idem_in_peirce_one**: If `jmul e f = f`, then `f ∈ P₁(e)`

2. **orthog_idem_peirce_one_le**: For orthogonal idempotents f, g: `P₁(f) ≤ P₁(f+g)`
   - Key insight: g ∈ P₀(f) implies `jmul g x = 0` for x ∈ P₁(f) by `peirce_mult_P0_P1`

3. **orthog_idem_peirce_one_lt**: For orthogonal f, g with g ≠ 0: `P₁(f) < P₁(f+g)`
   - Witness: g ∈ P₁(f+g) but g ∉ P₁(f) (since jmul f g = 0 ≠ g)

4. **sub_idem_finrank_lt**: `finrank P₁(f) < finrank P₁(e)` when `e = f + g` orthogonal

---

## Previous Session (48)

### Issue Cleanup

Closed stale issues for theorems that are fully proven:
- `af-w3sf`: primitive_peirce_one_dim_one (Primitive.lean:865-1064)
- `af-fbx8`, `af-utz0`: Same theorem, stale references
- `af-vaoe`: orthogonal_primitive_peirce_sq (Primitive.lean:1134)
- `af-eb7o`: orthogonal_primitive_structure (Primitive.lean:1287)

---

## Previous Session (47)

### ✅ isPrimitive_of_peirce_one_dim_one (Primitive.lean:1069-1100)

Added converse of `primitive_peirce_one_dim_one`:
```lean
theorem isPrimitive_of_peirce_one_dim_one {e : J} (he : IsIdempotent e) (hne : e ≠ 0)
    (hdim : Module.finrank ℝ (PeirceSpace e 1) = 1) : IsPrimitive e
```

**Key insight**: P₁(e) = ℝ·e when dim = 1. Any sub-idempotent f ∈ P₁(e) satisfies f = r • e.
Then jsq f = f gives r² = r, so r ∈ {0, 1}, hence f = 0 or f = e → e is primitive.

**Combined with `primitive_peirce_one_dim_one`**: Now have bidirectional characterization:
- `e primitive ⟺ finrank P₁(e) = 1`

This unblocks the induction approach for `exists_primitive_decomp`.

---

## Previous Session (46)

### ✅ Peirce Space Convenience Lemmas (Peirce.lean:47-53)

Added simp lemmas to simplify Peirce membership for eigenvalues 0 and 1:
- `mem_peirceSpace_zero_iff`: `a ∈ PeirceSpace e 0 ↔ jmul e a = 0`
- `mem_peirceSpace_one_iff`: `a ∈ PeirceSpace e 1 ↔ jmul e a = a`

### Closed Issues
- `af-0ysg`: Fix Peirce space eigenvalue form

---

## Previous Session (45)

### ✅ FormallyRealTrace Instance (Matrix/Trace.lean)

Added `formallyRealTraceHermitianMatrix` instance with:
- `traceReal_jsq_nonneg`: `0 ≤ traceReal (jsq A)`
- `traceReal_jsq_eq_zero_iff`: `traceReal (jsq A) = 0 ↔ A = 0`

Key helper: `traceReal_jsq_eq_traceInnerReal A : traceReal (jsq A) = traceInnerReal A A`

### ✅ orthogonal_primitive_structure (Primitive.lean:1251-1289)

Proved the H-O 2.9.4(iv) dichotomy:
```lean
theorem orthogonal_primitive_structure {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f) :
    (∀ a, jmul e a = (1/2) • a → jmul f a = (1/2) • a → a = 0) ∨
    IsStronglyConnected e f
```

**Proof strategy**:
- Case 1: All a in Peirce½(e) ∩ Peirce½(f) are zero → left disjunct
- Case 2: ∃ nonzero a → by `orthogonal_primitive_peirce_sq`, `jsq a = μ • (e+f)` with μ ≥ 0
  - μ > 0 (else jsq a = 0 ⟹ a = 0 by formal reality)
  - Let v = (√μ)⁻¹ • a, then jsq v = e + f → strongly connected

### Closed Issues
- `af-5zpv`: JordanTrace instance complete
- `af-2dzb`: trace_L_selfadjoint proven
- `af-pxqu`: FormallyRealTrace instance complete
- `af-xg63`: orthogonal_primitive_structure proven

---

## Previous Session (44)

### ✅ JordanTrace Instance Complete (Matrix/Trace.lean)

**Filled** two sorries in `AfTests/Jordan/Matrix/Trace.lean`:

1. **traceReal_smul** (line 220): `traceReal (r • A) = r * traceReal A`
2. **traceReal_L_selfadjoint** (line 252): `Tr((A∘V)∘W) = Tr(V∘(A∘W))`

**Result**: `jordanTraceHermitianMatrix` instance has no sorries.

---

## Previous Session (43)

### ✅ orthogonal_primitive_peirce_sq COMPLETE

**Completed** Step 12 (final step) in `Primitive.lean:1213-1244`:

- **Step 12**: `0 ≤ r₁` (non-negativity via formal reality)
  - Strategy: prove by contradiction using `FormallyRealJordan.sum_sq_eq_zero`
  - If `r₁ < 0`: form `jsq a + jsq (√(-r₁) • (e+f)) = 0` using `jsq_smul_idem hef_idem`
  - By formal reality, both summands are zero
  - `√(-r₁) • (e+f) = 0` with `√(-r₁) ≠ 0` implies `e + f = 0`
  - But `e + f = 0` contradicts orthogonality (would need `jmul e (-e) = 0`, i.e., `e = 0`)

**Key lemmas used**:
- `jsq_smul_idem he : jsq (r • e) = r² • e` (for idempotent e)
- `Real.sq_sqrt` - `(√x)² = x` for x ≥ 0
- `FormallyRealJordan.sum_sq_eq_zero` - formal reality property
- `smul_eq_zero`, `eq_neg_of_add_eq_zero_left`

**The theorem is now fully proven (12/12 steps, no sorry)!**

---

## Previous Session (42)

### Step 11: orthogonal_primitive_peirce_sq (r₁ = r₂)

**Added** Step 11 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1153-1212`:

- **Step 11**: `hr_eq : r₁ = r₂` (coefficient equality)
  - Key technique: Use Jordan identity `jordan_identity' a e` (and `jordan_identity' a f`)
  - Derive `jmul a (jsq a) = r₁ • a` and `jmul a (jsq a) = r₂ • a`
  - Conclude `(r₁ - r₂) • a = 0`, use `smul_eq_zero` to case split
  - If `a ≠ 0`: direct `linarith`
  - If `a = 0`: show `r₁ = r₂ = 0` via linear independence of orthogonal primitives

**Key lemmas used**:
- `jordan_identity' a e : jmul (jmul a e) (jsq a) = jmul a (jmul e (jsq a))`
- `jmul_smul`, `smul_jmul` - scalar pulling for Jordan product
- `smul_comm` - commutativity of scalar multiplication
- `smul_right_injective J h12ne` - injectivity when scalar ≠ 0
- `smul_eq_zero` - r • x = 0 ↔ r = 0 ∨ x = 0

---

## Previous Session (41)

### Steps 7-10: orthogonal_primitive_peirce_sq

**Added** Steps 7-10 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1133-1153`:

- **Step 7**: `hef_idem : IsIdempotent (e + f)`
- **Step 8**: `ha_in_P1_ef : a ∈ PeirceSpace (e + f) 1`
- **Step 9**: `hsq_in_P1_ef : jsq a ∈ PeirceSpace (e + f) 1`
- **Step 10**: `hsq_decomp : jsq a = r₁ • e + r₂ • f`

---

## Previous Session (40)

### Step 6: orthogonal_primitive_peirce_sq

**Added** Step 6 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1124-1131`:
- `hc₀e_zero : jmul e c₀e = 0` (c₀e ∈ P₀(e))
- `hjmul_e_sq : jmul e (jsq a) = r₁ • e` (symmetric to Step 5, using e-decomposition)

**Technique Note**: When rewriting with `IsIdempotent` (which is `jsq e = e`), need
to first convert `jmul e e` to `jsq e` using `← jsq_def` since `rw` doesn't unfold definitions.

---

## Previous Session (39)

### Helper Lemma: orthogonal_sum_isIdempotent

**Added** to `AfTests/Jordan/FormallyReal/Spectrum.lean:99-107`:
- `orthogonal_sum_isIdempotent` - sum of orthogonal idempotents is idempotent
- Required for Step 7 of `orthogonal_primitive_peirce_sq` proof

**Added** Step 4 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1113-1114`:
- `hf_in_P0_e : f ∈ PeirceSpace e 0` using `orthogonal_in_peirce_zero`
- `he_in_P0_f : e ∈ PeirceSpace f 0` using `orthogonal_in_peirce_zero horth.symm`

**Added** Step 5 to `orthogonal_primitive_peirce_sq` in `Primitive.lean:1116-1122`:
- `hjmul_f_sq : jmul f (jsq a) = r₂ • f`
- Uses f-decomposition and `c₀f ∈ P₀(f)` implies `jmul f c₀f = 0`

---

## Previous Session (38)

### JordanAlgebra Instance: Matrix/Instance.lean

**Created** `AfTests/Jordan/Matrix/Instance.lean` (126 LOC) with:
- `RealSymmetricMatrix` type alias for `selfAdjoint (Matrix n n ℝ)`
- `JordanAlgebra (RealSymmetricMatrix n)` instance

**Also added to JordanProduct.lean:**
- `jordanMul_add` - bilinearity (right)
- `add_jordanMul` - bilinearity (left)
- `smul_jordanMul` - scalar multiplication (left)
- `jordanMul_smul` - scalar multiplication (right)
- `jordan_identity` - the Jordan identity for matrices

**Key proof technique for Jordan identity:**
```lean
simp only [smul_add, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
conv_lhs => simp only [Matrix.mul_assoc]
conv_rhs => simp only [Matrix.mul_assoc]
ring_nf; abel
```

---

## Current State

### Jordan Algebra Project
- 38 files, ~7,991 LOC total
- **15 sorries remaining** across 8 files:
  - `FundamentalFormula.lean:151` — `fundamental_formula` (needs Macdonald's theorem)
  - `Quadratic.lean:134` — `U_idempotent_comp` (provable via Peirce polynomial)
  - `SpectralTheorem.lean:59,71,80,159,162,173` — 6 sorries (spectral decomposition chain)
  - `FormallyReal/Def.lean:75,80` — `of_sq_eq_zero` (accepted gap, circular dependency)
  - `FormallyReal/Square.lean:102,118` — sqrt uniqueness + existence (needs spectral)
  - `FormallyReal/Spectrum.lean:146` — eigenvalue non-negativity (needs spectral)
  - `Classification/RealSymmetric.lean:81` — isSimple (needs matrix units)
  - `Classification/ComplexHermitian.lean:78` — isSimple (needs matrix units)
- Matrix Jordan algebra has full instance
- Primitive idempotent theory COMPLETE (Sessions 39-55)
- Triple product identities (2.42)-(2.44) COMPLETE (Sessions 63-66)

### Archimedean Closure Project: COMPLETE
- 44 files, 4,943 LOC, 0 sorries

### Progress by H-O Chapter
- Ch 2 (identities, operators): ~85%
- Ch 2.6 (Peirce): ~95%
- Ch 2.9 (primitives): ~95%
- Ch 3.1-3.2 (formally real, spectral): ~40%
- Ch 3.3-3.5 (classification): ~15%

---

## Next Steps

### Critical Path A: Power Formulas
1. **`af-jify` (P1, READY)**: `L_jpow_comm_all` — all power L-operators commute (H-O 2.4.5(ii))
   - Strong induction on l using operator_formula recursion, ~50-80 LOC
2. **`af-u0tp` (P1, blocked on jify)**: Power formulas (2.45)-(2.46)
   - (2.45): `2·T_{a^l} · U_{a^m, a^n} = U_{a^{m+l}, a^n} + U_{a^m, a^{n+l}}`
   - (2.46): `U_{a^n} = U_a^n` (by induction using (2.45) twice)

### Critical Path B: Fundamental Formula (unblocked)
1. **`af-tggl` (P1, READY)**: Macdonald's theorem (H-O 2.4.13) — ~200+ LOC
2. **`af-i8oo` (P1, blocked on tggl)**: Fundamental formula `U_{U_a(b)} = U_a U_b U_a`

### Critical Path C: Spectral Theorem (unblocked)
1. **`af-s4t7` (P1, READY)**: `spectral_decomposition_exists` — ~80-100 LOC
   - All Primitive.lean dependencies are resolved (sessions 39-55)
2. `af-102j`, `af-rcy0`, `af-vulx` (P2, blocked on s4t7): downstream spectral chain

### Quick Wins (unblocked)
- **`af-a5qq` (P2, READY)**: `U_idempotent_comp` — provable via Peirce polynomial identity, ~35 LOC
- **`af-zi08` (P2, READY)**: RealSymmetric.isSimple — matrix units approach, ~170 LOC

### Deferred (P3)
- `af-tpm2`: of_sq_eq_zero — accepted gap (circular dependency)
- Classification downstream: envelope, reversible, spin factors, quaternions (~15 issues)

---

## Files Modified This Session

- `HANDOFF.md` (updated)
- Beads: closed af-gk4c, created af-jify, added dependency af-u0tp→af-jify

---

## Sorries (15 total, 8 files)

| File | Line | Theorem | Issue | Blocker |
|------|------|---------|-------|---------|
| FundamentalFormula.lean | 151 | `fundamental_formula` | af-i8oo (P1) | Macdonald's theorem |
| Quadratic.lean | 134 | `U_idempotent_comp` | af-a5qq (P2) | None (Peirce polynomial) |
| SpectralTheorem.lean | 59 | `spectral_decomposition_exists` | af-s4t7 (P1) | None (unblocked) |
| SpectralTheorem.lean | 71 | `spectral_decomposition_finset` | af-102j (P2) | af-s4t7 |
| SpectralTheorem.lean | 80 | `spectrum_eq_eigenvalueSet` | af-rcy0 (P2) | af-s4t7 |
| SpectralTheorem.lean | 159,162 | `spectrum_sq` | af-vulx (P2) | af-rcy0 |
| SpectralTheorem.lean | 173 | `sq_eigenvalues_nonneg` | af-gbmu (P3) | af-vulx |
| FormallyReal/Def.lean | 75,80 | `of_sq_eq_zero` | af-tpm2 (P3) | Circular (accepted gap) |
| FormallyReal/Square.lean | 102 | `isPositiveSqrt_unique` | af-o95c (P3) | af-s4t7 |
| FormallyReal/Square.lean | 118 | `HasPositiveSqrt.of_positiveElement` | af-uifg (P3) | af-s4t7 |
| FormallyReal/Spectrum.lean | 146 | `spectral_sq_eigenvalues_nonneg` | af-1vkv (P3) | af-vulx |
| Classification/RealSymmetric.lean | 81 | `isSimple` | af-zi08 (P2) | None |
| Classification/ComplexHermitian.lean | 78 | `isSimple` | af-4uo9 (P2) | af-zi08 |

---

## Technical Notes

### Jordan Identity Proof Pattern
The Jordan identity `(A ∘ B) ∘ A² = A ∘ (B ∘ A²)` for matrices:
1. Expand using `jordanMul_def` and `jordanMul_self`
2. Pull scalars through with `smul_mul_assoc`, `mul_smul_comm`
3. Apply `Matrix.mul_assoc` using `conv` to both sides
4. Terms become identical after `ring_nf; abel`

### HermitianMatrix vs RealSymmetricMatrix
- `HermitianMatrix n R` works for general `[Field R] [StarRing R]`
- `RealSymmetricMatrix n` = `selfAdjoint (Matrix n n ℝ)` has `Module ℝ` automatically
- Only RealSymmetricMatrix gets JordanAlgebra instance (over ℝ)

---

## Beads Summary (Session 68)

- **Closed**: af-gk4c (jpow_add already proved)
- **Created**: af-jify (L_jpow_comm_all, P1) — blocks af-u0tp
- **3 critical paths** remain: power formulas (needs af-jify), fundamental formula, spectral theorem

---

## Previous Sessions

### Session 37 (2026-01-30)
- Eliminated IsHermitian.jordanMul sorry
- Documented of_sq_eq_zero limitation

### Session 36 (2026-01-30)
- Jordan FormallyReal properties, cone, matrix product (3 files, 269 LOC)

### Session 35 (2026-01-30)
- Jordan algebra core infrastructure (5 files, 460 LOC)
