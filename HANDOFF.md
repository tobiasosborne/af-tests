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
  - Proved both halves of the x and y pure/long branches:
    `eq258_xCons_one_yCons_xCons_ge`,
    `eq258_xCons_one_yCons_xCons_lt`,
    `eq258_yCons_one_xCons_yCons_ge`, and
    `eq258_yCons_one_xCons_yCons_lt`.
  - Added driver-ready combined wrappers:
    `eq258X_xCons_one_yCons_xCons_from_driverIH` and
    `eq258Y_yCons_one_xCons_yCons_from_driverIH`.
  - Added the long swap bridge lemmas:
    `eq258X_yCons_xCons_xCons_one_from_driverIH_comm` and
    `eq258Y_xCons_yCons_yCons_one_from_driverIH_comm`. These apply the new
    swapped pure/long Eq258 branches through `Eq258X_of_swapped_comm` /
    `Eq258Y_of_swapped_comm`, leaving only the recursive `M_op` symmetry facts
    required by the reducer lemmas.
- Eliminated the long boundary swap-layer blocker:
  - Added small direct unfold lemmas for the pure boundary and non-WF same-letter
    boundary cases where broad `simp [M_op.eq_def]` loops.
  - Proved the mutual `M_op` symmetry package:
    `M_op_one_comm`, `M_op_xCons_one_yCons_comm`, and
    `M_op_yCons_one_xCons_comm`.
  - Added `Eq258DriverWFLayer.of_driverIH`, deriving the well-formed current
    boundary swap layer directly from `Eq258DriverIH`.
  - Added direct driver-IH long boundary wrappers:
    `eq258X_xCons_yCons_one_from_driverIH` and
    `eq258Y_yCons_xCons_one_from_driverIH`.
- Added complete well-formed driver dispatchers:
  - `eq258X_of_driverIH_of_inX_inY` covers all H-O x-direction alternating
    cases under `p ∈ X`, `q ∈ Y`, and `WF` side conditions.
  - `eq258Y_of_driverIH_of_inY_inX` covers the symmetric y-direction cases.
  - These dispatchers are the single case-split entry points for the final
    recursive driver once it reduces goals to well-formed monomial shapes.
- Scoped the next driver package:
  - Added `Eq258DriverWFCore`, a narrower induction package recording
    well-formed ordinary Eq258 facts and the safe raw-right boundary facts
    currently known to be true.
  - Added `Eq258DriverWFCore.of_driverIH` to show the older broad
    `Eq258DriverIH` still implies the narrower core.
  - Important finding: the cross raw-right facts generated by the `<` branch
    must not be baked into the induction package as plain theorem-family facts.
    Some right-start same-letter raw goals unfold into the total-syntax
    non-WF clauses of `M_op`, outside H-O's side-conditioned theorem.
- Added the easy raw-right boundary base cases:
  - `eq258XRawRight_one_one` and `eq258YRawRight_one_one`.
  - `eq258XRawRight_yCons_one_one` and `eq258YRawRight_xCons_one_one`.
  - These close directly after unfolding the boundary `M_op` definitions and
    commuting the pure opposite powers.
- Refactored the long `<` branch lower-pair interface:
  - Added local obligations `Eq258XLowerLeft` and `Eq258YLowerLeft`.
  - Added compatibility adapters `Eq258XLowerLeft.of_rawRight` and
    `Eq258YLowerLeft.of_rawRight`.
  - Added lower-obligation wrappers:
    `eq258_xCons_yCons_general_lt_from_lower_obligations`,
    `eq258_xCons_yCons_general_from_lower_obligations`,
    `eq258_yCons_xCons_general_lt_from_lower_obligations`, and
    `eq258_yCons_xCons_general_from_lower_obligations`.
  - Existing raw-right wrappers now route through these lower-obligation
    wrappers, and the driver-IH constructor wrappers call the lower interface
    directly with an explicit compatibility conversion.
- Realigned the long constructor branch with Hanche-Olsen's actual proof shape:
  - Added `Eq258LongBranchIH`, a local package for exactly the recursive
    obligations appearing in H-O's long calculation: the swapped term, the
    opposite-generator base term, the left lower-pair term, and the ordinary
    right lower-pair term.
  - Added `Eq258LongBranchIH.of_driverIH` only as a compatibility bridge from
    the older broad `Eq258DriverIH`.
  - Added `eq258X_xCons_yCons_from_longBranchIH` and
    `eq258Y_yCons_xCons_from_longBranchIH`; the legacy
    `..._from_driverIH` wrappers now delegate through the H-O-shaped package.
- Began the direct H-O recurrence migration requested after rereading
  `joa-m.md` lines 1258-1266 and 1326-1377:
  - Changed the different-letter `M_op` recurrence in `MOperator.lean` so the
    second recursive argument uses concatenation (`prependX`/`prependY`) rather
    than raw `xCons`/`yCons`, matching H-O (2.55a,b).
  - Added `weight_prependX`, `weight_prependY`, `prependX_prependX`, and
    `prependY_prependY` in `MonoBlock.lean` for termination and concatenation
    normalization.
  - Updated `MOperatorProperties.lean` recurrence/property (iv) statements to
    the concatenated form; `lake build AfTests.Jordan.Macdonald.MOperatorProperties`
    passes.
  - Started migrating `Equation258.lean` lower-left/raw-right and long-branch
    helper interfaces from raw right constructors to `prependX`/`prependY`.
- Finished the `Equation258.lean` H-O recurrence migration:
  - Updated the equal-index long branches to distribute `U` first and then use
    `M_op_U_prependX` / `M_op_U_prependY`, matching the concatenated (2.55)
    recurrence instead of forcing raw constructor terms.
  - Updated the same-letter lower-pair branches to target `prependX` /
    `prependY` terms and normalize nested concatenations before the final
    H-O cancellations.
  - Replaced brittle weight proofs that unfolded `prependX`/`prependY` with
    `weight_prependX` and `weight_prependY`.
  - Verified `eq258X_of_driverIH_of_inX_inY` and
    `eq258Y_of_driverIH_of_inY_inX` with only standard Lean axioms
    (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`.
- Advanced the final-driver symmetry prerequisites:
  - Added `M_op_xCons_yCons_comm_WF` and `M_op_yCons_xCons_comm_WF`, mutual
    well-formed different-letter commutativity lemmas for H-O property (ii).
    These cover the long/long swapped terms that the final side-conditioned
    induction needs, without asserting false commutativity for arbitrary
    non-WF total syntax.
  - Added merged-prepend commutativity wrappers
    `M_op_prependY_prependX_comm_WF` and
    `M_op_prependX_prependY_comm_WF` for the exact concatenated products
    produced by H-O (2.55)/(2.58).
  - Added `prependX_inX`, `prependY_inY`, `WF_prependX_of_inX`, and
    `WF_prependY_of_inY` in `MonoBlock.lean`, so merged prepends can be fed
    back into the well-formed dispatcher layer.
- Pushed the WF symmetry package through the next long-branch layer:
  - Added general `M_op_comm_WF`, proving H-O property (ii) for all
    well-formed alternating monomials by recursion on total block weight.
  - Added `WF_prependX_of_inY` and `WF_prependY_of_inX`, covering the
    non-merging prepend/WF cases needed by symmetry transfers.
  - Added WF-specialized swapped Eq258 adapters:
    `Eq258X_of_swapped_comm_WF`, `Eq258Y_of_swapped_comm_WF`,
    `Eq258XLowerLeft.of_swapped_eq258X_comm_WF`, and
    `Eq258YLowerLeft.of_swapped_eq258Y_comm_WF`.
  - Added `Eq258DriverWFCore.xSwapped`, `.ySwapped`,
    `.xLowerLeftSwapped`, and `.yLowerLeftSwapped`, deriving swapped
    H-O induction calls from the side-conditioned core plus property (ii).
  - Added long constructor wrappers
    `eq258X_xCons_yCons_from_wfCore_sameY` and
    `eq258Y_yCons_xCons_from_wfCore_sameX`. These show the genuinely long
    branches now need only one extra recursive family: same-side lower-right
    facts (`Eq258X` on two `Y` monomials and `Eq258Y` on two `X` monomials).
  - Updated the well-formed dispatchers to use those WF-core long-branch
    wrappers, keeping the old broad `Eq258DriverIH` only as the current
    compatibility source for the remaining same-side lower-right facts.

## Current State
- Build status: passing.
- Passing checkpoints:
  - `lake env lean AfTests/Jordan/Macdonald/MonoBlock.lean`
  - `lake env lean AfTests/Jordan/Macdonald/Equation258.lean`
  - `lake build AfTests.Jordan.Macdonald.MonoBlock`
  - `lake build AfTests.Jordan.Macdonald.Equation258`
  - `lake build AfTests`
- Sorry count: `Equation258.lean` and the touched Macdonald support files have
  no `sorry`, `admit`, `axiom`, or `unsafe` source occurrences.
- Axiom status for the Eq258 dispatcher theorems, `M_op_comm_WF`, the
  WF-core swapped adapters, and the new WF-core long wrappers: no `sorryAx`;
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Open blockers:
  - The final driver still needs the global recursive case split, but that
    should now build on the H-O-aligned dispatcher layer.
  - Current `bd` embedded Dolt store reports no open issues but still has
    runtime state dirty under `.beads`; do not stage `.beads` runtime files.

## Next Steps (Priority Order)
1. Add the side-conditioned same-side lower-right package: `Eq258X` for
   well-formed `Y/Y` lower pairs and `Eq258Y` for well-formed `X/X` lower pairs.
   This is now the isolated hard input to the H-O long branches.
2. Build the final recursive simultaneous induction driver for Eq(2.58) on top
   of `eq258X_of_driverIH_of_inX_inY`, `eq258Y_of_driverIH_of_inY_inX`, and the
   narrowed WF-core/same-side adapters.
3. Migrate or restore the old JSONL Beads so `bd ready` reflects the historical issue queue.

## Known Issues / Gotchas
- Always read `examples3/Jordan Operator Algebras/joa-m/joa-m.md` before Macdonald work.
- Hanche-Olsen does not prove a broad raw-right theorem over arbitrary
  total syntax. The long `<` branch uses ordinary induction on (iv),
  property (iii), and local lower-pair algebra. Do not expand
  `Eq258DriverIH.rawRight` to cover non-H-O cases.
- Use `lake build AfTests 2>&1 | tail -40`, not bare `lake build`.
- `M_op.eq_def` can loop under broad `simp`; prefer targeted rewrites.
- The useful `M_op` symmetry package is not full arbitrary `M_op p q`
  commutativity. It covers boundary symmetry against `1` and pure-vs-opposite-
  start symmetry, exactly the shapes exposed by (2.56)/(2.57) and the long
  boundary swap reducers.
- `M_op_xCons_yCons_comm_WF` / `M_op_yCons_xCons_comm_WF` are the full
  different-letter symmetry lemmas to use under H-O well-formed side
  conditions. For merged H-O products, prefer
  `M_op_prependY_prependX_comm_WF` and
  `M_op_prependX_prependY_comm_WF`.
- `M_op_comm_WF` is now the preferred H-O property (ii) lemma for arbitrary
  well-formed alternating monomials. Use it through the WF-specific Eq258
  adapters where possible rather than hand-threading three commutativity facts.
- `bd ready` currently reports no open issues, but `bd show af-0llu` hit an embedded
  Dolt exclusive-lock error in this session. Do not assume Beads state is complete.
- `bd create` currently fails with `database not initialized: issue_prefix config
  is missing`; do not initialize a new prefix until the old JSONL/Dolt state has
  been reconciled.
- `bd sync` is not available in the installed bd CLI, and `bd dolt push` fails
  because the embedded Dolt database has no `origin` remote configured.
- `Eq258YBaseObligation` is intentionally an assumption to the x-direction helpers. It
  records a real y-direction induction obligation rather than hiding it behind a local sorry.
- `prependY_of_inX` and `prependX_of_inY` already exist in `MonoBlock.lean`; use them
  for side-condition conversions.
- `prependX_prependX` / `prependY_prependY` are now available for nested H-O
  concatenation. Use them before algebraic `module`/`abel_nf` steps.
- After correcting (2.55), ordinary helper adapters like
  `eq258X_xCons_right_of_eq258X` and `eq258Y_yCons_right_of_eq258Y` may be too
  raw for swapped long-branch terms. Prefer direct `Eq258X`/`Eq258Y` facts on
  `prependX i s` / `prependY j s`.
- Do not stage `.beads` runtime/Dolt files unless explicitly working on Beads migration.

## Files Modified
- `AfTests/Jordan/Macdonald/Equation258.lean`
- `AfTests/Jordan/Macdonald/MonoBlock.lean`
- `HANDOFF.md`
