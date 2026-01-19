import AfTests.Core
import AfTests.ThreeCycle.Lemma06
import AfTests.ThreeCycle.Lemma07
import AfTests.ThreeCycle.Lemma08
import Mathlib.GroupTheory.Perm.Cycle.Type

open Equiv Perm

-- For comprehensive coverage, let me check all products for n=1,k=1,m=1
-- c₁₂ * c₁₃⁻¹
#eval ((commutator_g₁_g₂ 1 1 1 * (commutator_g₁_g₃ 1 1 1)⁻¹) ^ 2).cycleType  -- {3,3}
-- c₁₂ * c₂₃⁻¹  
#eval ((commutator_g₁_g₂ 1 1 1 * (commutator_g₂_g₃ 1 1 1)⁻¹) ^ 2).cycleType
-- c₁₃ * c₂₃⁻¹
#eval ((commutator_g₁_g₃ 1 1 1 * (commutator_g₂_g₃ 1 1 1)⁻¹) ^ 2).cycleType  -- {3,3}
-- c₁₃ * c₁₂⁻¹
#eval ((commutator_g₁_g₃ 1 1 1 * (commutator_g₁_g₂ 1 1 1)⁻¹) ^ 2).cycleType
-- c₂₃ * c₁₂⁻¹
#eval ((commutator_g₂_g₃ 1 1 1 * (commutator_g₁_g₂ 1 1 1)⁻¹) ^ 2).cycleType
-- c₂₃ * c₁₃⁻¹
#eval ((commutator_g₂_g₃ 1 1 1 * (commutator_g₁_g₃ 1 1 1)⁻¹) ^ 2).cycleType

-- Triple product
#eval ((commutator_g₁_g₂ 1 1 1 * commutator_g₁_g₃ 1 1 1 * commutator_g₂_g₃ 1 1 1) ^ 2).cycleType
