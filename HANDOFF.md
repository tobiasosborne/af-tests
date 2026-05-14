# Handoff: 2026-05-14

## Completed This Session
- Eliminated the remaining `Equation258.lean` sorry without adding an axiom or keeping the
  over-strong `eq258_y_base` theorem.
- Replaced `eq258_y_base` with explicit theorem-family propositions:
  - `Eq258X`: x-direction H-O (2.58) shape.
  - `Eq258Y`: y-direction companion shape.
  - `Eq258YBaseObligation`: the concrete y-base obligation needed by the x-direction
    weight>1 helpers.
- Threaded `Eq258YBaseObligation` through both x-direction inductive helpers:
  - `eq258_xCons_yCons_general_ge`
  - `eq258_xCons_yCons_general_lt`
- Confirmed `AfTests/Jordan/Macdonald/Equation258.lean` has no `sorry`/`admit` source
  occurrences and compiles.
- Added the first driver-adapter layer:
  - `eq258YBaseObligation_of_eq258Y` converts `Eq258Y` plus `s.inX` into the concrete
    y-base obligation.
  - `eq258X_xCons_right_of_eq258X` converts an `Eq258X` hypothesis into the swapped
    `ih_swap` shape.
  - `eq258X_yCons_yCons_lower_of_eq258X` converts the right lower-pair fact from
    `Eq258X`.
  - `Eq258XRawRight` names the raw unmerged right-product obligation produced by the
    current recurrence-helper algebra.
  - New `_from_families` wrappers for the `i ≥ k` and `i < k` weight>1 helpers.
  - `eq258_xCons_yCons_general_from_family_obligations` combines the `i ≥ k`/`i < k`
    split behind one constructor-case theorem for the future driver.
- Started the actual driver scaffold:
  - Added `Eq258DriverIH`, a weight-indexed simultaneous IH package over total
    `FreeAssocMono` shapes.
  - Added `eq258X_xCons_yCons_from_driverIH`, proving the weight>1
    `xCons (yCons ...) / yCons ...` constructor case from `Eq258DriverIH`.
  - Added driver-ready `Eq258X` wrappers for the existing weight≤1 x-direction cases.
- Started the y-side mirror:
  - Added `Eq258YRawRight` and included it in `Eq258DriverIH`.
  - Added `Eq258XBaseObligation` plus adapters for the future y-direction helpers.
  - Proved `U_bilinear_y_pow_lt_as_U_T`.
  - Proved the pure-power y-direction base cases `eq258_yCons_xCons_ge` and
    `eq258_yCons_xCons_lt`, and wrapped the easy y weight≤1 cases as `Eq258Y` lemmas.
  - Proved the full y-symmetric weight>1 helper pair:
    `eq258_yCons_xCons_general_ge` and `eq258_yCons_xCons_general_lt`.
  - Added y-side family wrappers and `eq258Y_yCons_xCons_from_driverIH`.
- Advanced the one-argument boundary layer:
  - Added the four H-O (2.56)/(2.57) recurrence wrappers:
    `eq259_xCons_one`, `eq259_yCons_one`, `eq259_one_xCons`, `eq259_one_yCons`.
  - Added exact Eq(2.58) consequences obtained by rearranging those recurrences:
    `eq258X_yCons_one_exact`, `eq258Y_xCons_one_exact`,
    `eq258X_one_yCons_exact`, `eq258Y_one_xCons_exact`.
  - Proved the pure-power boundary cases with second argument `1`:
    `eq258_xCons_one_ge`, `eq258_xCons_one_lt`,
    `eq258_yCons_one_ge`, `eq258_yCons_one_lt`.
  - Added driver-ready wrappers `eq258X_xCons_one_one` and `eq258Y_yCons_one_one`.
- Proved the hard long one-argument boundary algebra:
  - Added `eq258_xCons_one_general_ge` and `eq258_xCons_one_general_lt`.
  - Added `eq258_yCons_one_general_ge` and `eq258_yCons_one_general_lt`.
  - Added family-obligation adapters:
    `eq258X_xCons_yCons_one_from_family_obligations` and
    `eq258Y_yCons_xCons_one_from_family_obligations`.
  - Added exact left-boundary adapters:
    `eq258X_one_yCons_xCons_exact` and `eq258Y_one_xCons_yCons_exact`.
  - Key finding: the long boundary expansion of `M(x_i r, 1)` produces the swapped
    same-total-weight term `M(r, x_i)`. That obligation is now explicit in the
    helper statements; it is not available from the current total-weight-only
    `Eq258DriverIH`.
- Added the current-weight driver layer for those same-weight boundary swaps:
  - `Eq258DriverLayer` packages strict lower-weight facts from `Eq258DriverIH` plus
    the current-weight swapped boundary obligations.
  - `eq258XRawRight_of_eq258X_of_inY` and `eq258YRawRight_of_eq258Y_of_inX` recover
    raw-right lower facts from ordinary Eq258 families when both arguments are on the
    non-merging side.
  - `eq258X_xCons_yCons_one_from_driverLayer` and
    `eq258Y_yCons_xCons_one_from_driverLayer` prove the long right-boundary
    constructor cases from `Eq258DriverLayer`.
- Began formalizing the H-O symmetry step for swapped same-weight boundary facts:
  - Added `M_op_yCons_one_xCons_one_comm`,
    `M_op_xCons_one_xCons_yCons_one_comm`, and
    `M_op_yCons_one_yCons_xCons_one_comm`.
  - Added swapped pure-power base families:
    `eq258X_yCons_one_xCons_one` and `eq258Y_xCons_one_yCons_one`.
- Refined the long boundary layer to match the well-formed H-O cases:
  - Added `Eq258DriverWFLayer`, which keeps strict lower facts in
    `Eq258DriverIH` and only packages genuinely long same-weight boundary swaps.
  - Added `Eq258DriverWFLayer.xBoundarySwap` and `.yBoundarySwap`, discharging
    the pure-tail swaps via the swapped weight≤1 base lemmas.
  - Added `eq258X_xCons_yCons_one_from_wfDriverLayer` and
    `eq258Y_yCons_xCons_one_from_wfDriverLayer`, so the long one-argument
    boundary constructors now consume the narrower well-formed layer.
- Made the next H-O symmetry obligation explicit:
  - Added `Eq258X_of_swapped_comm` and `Eq258Y_of_swapped_comm`, generic
    symmetry-transfer lemmas for Eq(2.58).
  - Added recurrence-level commutativity reducers:
    `M_op_yCons_xCons_xCons_one_comm_of`,
    `M_op_xCons_yCons_yCons_one_comm_of`,
    `M_op_xCons_one_xCons_yCons_xCons_comm_of`, and
    `M_op_yCons_one_yCons_xCons_yCons_comm_of`.
    These deliberately take lower symmetry facts as hypotheses rather than
    claiming false total-syntax commutativity for non-well-formed branches.
- Advanced the swapped pure/long boundary branch needed by the long symmetry path:
  - Added `M_op_U_bilinear_one_xCons` and `M_op_U_bilinear_one_yCons`, the
    pure/long counterparts to the existing different-letter `M_op_U_bilinear_*`
    rearrangements.
  - Proved the `i ≥ k` / `j ≥ l` halves:
    `eq258_xCons_one_yCons_xCons_ge` and
    `eq258_yCons_one_xCons_yCons_ge`.
  - Added driver-ready wrappers:
    `eq258X_xCons_one_yCons_xCons_ge_from_driverIH` and
    `eq258Y_yCons_one_xCons_yCons_ge_from_driverIH`.

## Current State
- Build status: passing (`lake build AfTests 2>&1 | tail -40`, 1915 jobs).
- Sorry count: 8 actual sorries across `AfTests`.
- `Equation258.lean`: sorry-free.
- Open blockers:
  - Eq(2.58) still needs the recursive driver itself. The main weight>1 x and y
    constructor branches now have driver-ready theorems.
  - The long one-argument boundary branches are proven as algebraic adapters.
    The remaining hard driver question is proving the genuinely long swap fields
    in `Eq258DriverWFLayer`:
    `Eq258X k (yCons m (xCons l r')) (xCons i one)` and
    `Eq258Y l (xCons m (yCons n r')) (yCons j one)`.
  - The H-O symmetry path is now formalized as a bridge plus lower-commutativity
    reducers. The next missing ingredient is an induction package proving the
    required lower `M_op` symmetry facts for well-formed boundary shapes, then
    feeding them through `Eq258X_of_swapped_comm` / `Eq258Y_of_swapped_comm`.
  - The swapped pure/long branch is now done in the easy `≥` case on both x and
    y sides. The `<` case remains and should mirror the already-proven
    `eq258_xCons_yCons_general_lt` / `eq258_yCons_xCons_general_lt` pattern,
    with lower raw-right facts for the pure/long shapes.
  - In the `<` helpers, the left lower-pair facts are named as `Eq258XRawRight` /
    `Eq258YRawRight`. This keeps the existing proof honest: the helper algebra needs
    the unnormalized products `xCons (k - i - 1) q` and `yCons (l - j - 1) q`, not
    `prependX` / `prependY`.
  - Current `bd` embedded Dolt store is empty; old issue data lives in `.beads/issues.jsonl`.

## Next Steps (Priority Order)
1. Prove the lower `M_op` symmetry package for well-formed boundary shapes
   exposed by the new `_comm_of` lemmas, then instantiate the long swap fields
   required by `Eq258DriverWFLayer`.
2. Finish the `<` halves of the swapped pure/long boundary branch:
   `Eq258X k (xCons i one) (yCons j (xCons l r))` for `i < k`, and the y-side
   mirror for `j < l`.
3. Build the recursive simultaneous induction over the new layer, reusing
   `Eq258DriverIH` for strict total-weight decreases.
4. Migrate or restore the old JSONL Beads so `bd ready` reflects the historical issue queue.

## Known Issues / Gotchas
- Always read `examples3/Jordan Operator Algebras/joa-m/joa-m.md` before Macdonald work.
- Use `lake build AfTests 2>&1 | tail -40`, not bare `lake build`.
- `M_op.eq_def` can loop under broad `simp`; prefer targeted rewrites.
- `bd ready` currently reports no open issues, but `bd show af-0llu` hit an embedded
  Dolt exclusive-lock error in this session. Do not assume Beads state is complete.
- `Eq258YBaseObligation` is intentionally an assumption to the x-direction helpers. It
  records a real y-direction induction obligation rather than hiding it behind a local sorry.
- `prependY_of_inX` and `prependX_of_inY` already exist in `MonoBlock.lean`; use them
  for side-condition conversions.
- Do not stage `.beads` runtime/Dolt files unless explicitly working on Beads migration.

## Files Modified
- `AfTests/Jordan/Macdonald/Equation258.lean`
- `HANDOFF.md`
