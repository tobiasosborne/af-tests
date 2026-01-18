/-
  AfTests.Core - Root module for core definitions

  This module re-exports all core components needed for the AF-Tests formalization:
  - Omega: The permutation domain Fin(6+n+k+m)
  - Generators: The three generators g₁, g₂, g₃
  - GroupH: The subgroup H = ⟨g₁, g₂, g₃⟩
  - Blocks: Block structure for primitivity analysis
-/

import AfTests.Core.Omega
import AfTests.Core.Generators
import AfTests.Core.GroupH
import AfTests.Core.Blocks
