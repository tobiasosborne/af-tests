# Proof Export

## Node 1

**Statement:** |H_6| = 24 < 360 = |A_6|, hence H_6 is not equal to A_6 or S_6.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** We prove H_6 ∉ {A_6, S_6} by showing the cardinalities are distinct. The proof proceeds in three parts:

Part 1: By Lemma 3 (Base Case Structure), H_6 ≅ S_4, hence |H_6| = |S_4| = 4! = 24.

Part 2: We compute |A_6| = 6!/2 = 720/2 = 360 and |S_6| = 6! = 720.

Part 3: Since |H_6| = 24 < 360 = |A_6| < 720 = |S_6|, and unequal cardinalities imply distinct groups (by Subgroup_Cardinality), we conclude H_6 ∉ {A_6, S_6}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** Part 1: |H_6| = 24.

By Lemma 3 (Base Case Structure) from the external reference lemma03_base_case_structure, we have H_6 ≅ S_4.

Since isomorphic groups have equal cardinality:
|H_6| = |S_4|.

By definition of the symmetric group S_4 and the Factorial definition:
|S_4| = 4! = 4 × 3 × 2 × 1 = 24.

Therefore, |H_6| = 24.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** Part 2: |A_6| = 360 and |S_6| = 720.

By definition, S_6 is the symmetric group on 6 elements, so by the Factorial definition:
|S_6| = 6! = 6 × 5 × 4 × 3 × 2 × 1 = 720.

By definition, A_6 is the alternating group on 6 elements, which consists of all even permutations in S_6. The alternating group has index 2 in the symmetric group, so:
|A_6| = |S_6|/2 = 720/2 = 360.

Therefore, |A_6| = 360 and |S_6| = 720.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** Part 3: Conclusion that H_6 ∉ {A_6, S_6}.

From Part 1: |H_6| = 24.
From Part 2: |A_6| = 360 and |S_6| = 720.

We observe:
- |H_6| = 24 ≠ 360 = |A_6|
- |H_6| = 24 ≠ 720 = |S_6|

By the Subgroup_Cardinality definition: if |H| ≠ |G|, then H ≠ G.

Applying this principle:
- Since |H_6| ≠ |A_6|, we have H_6 ≠ A_6.
- Since |H_6| ≠ |S_6|, we have H_6 ≠ S_6.

Therefore, H_6 ∉ {A_6, S_6}, completing the proof of Lemma 4 (Base Case Exclusion).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

