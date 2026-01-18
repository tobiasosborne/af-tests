/-
  AfTests - Root module for the AF-Tests formalization project

  This module re-exports all components of the formalization proving:
  H = ⟨g₁, g₂, g₃⟩ equals Aₙ (if n,k,m all odd) or Sₙ (otherwise)
  for Ω = Fin(6+n+k+m).

  ## Structure

  - Core: Fundamental definitions (Omega, Generators, GroupH, Blocks)
  - BaseCase: Lemmas 1-4 (base case n=k=m=0)
  - Transitivity: Lemma 5 (H acts transitively)
  - ThreeCycle: Lemmas 6-9 (commutators and 3-cycle extraction)
  - Primitivity: Lemmas 10-11 (H acts primitively when n+k+m≥1)
  - SignAnalysis: Lemmas 12-15 (Jordan, sign, parity, classification)
  - MainTheorem: Final result combining all lemmas
-/

-- Legacy example files
import AfTests.Basic
import AfTests.Sqrt2Irrational
import AfTests.InfinitelyManyPrimes

-- ============================================
-- CORE DEFINITIONS
-- ============================================
import AfTests.Core

-- ============================================
-- BASE CASE (Lemmas 1-4)
-- ============================================
import AfTests.BaseCase.Lemma01
import AfTests.BaseCase.Lemma02
import AfTests.BaseCase.Lemma03
import AfTests.BaseCase.Lemma04

-- ============================================
-- TRANSITIVITY (Lemma 5)
-- ============================================
import AfTests.Transitivity.Lemma05

-- ============================================
-- THREE-CYCLE EXTRACTION (Lemmas 6-9)
-- ============================================
import AfTests.ThreeCycle.Lemma06
import AfTests.ThreeCycle.Lemma07
import AfTests.ThreeCycle.Lemma08
import AfTests.ThreeCycle.Lemma09

-- ============================================
-- PRIMITIVITY (Lemmas 10-11)
-- ============================================
import AfTests.Primitivity.Lemma10
import AfTests.Primitivity.Lemma11_1
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_3
import AfTests.Primitivity.Lemma11_4
import AfTests.Primitivity.Lemma11_5
import AfTests.Primitivity.Lemma11

-- ============================================
-- SIGN ANALYSIS (Lemmas 12-15)
-- ============================================
import AfTests.SignAnalysis.Lemma12
import AfTests.SignAnalysis.Lemma13
import AfTests.SignAnalysis.Lemma14
import AfTests.SignAnalysis.Lemma15

-- ============================================
-- MAIN THEOREM
-- ============================================
import AfTests.MainTheorem
