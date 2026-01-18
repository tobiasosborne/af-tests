# Proof Export

## Node 1

**Statement:** Suppose n >= 1 and H preserves a block system B on Omega. Let B be the block containing a_1. If g_1(B) = B, then supp(g_1) is contained in B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: Direct application of Lemma 11.2 to the cycle g_1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** PREMISE: n ≥ 1, so a_1 exists. Let B be the block containing a_1. Assume g_1(B) = B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** CYCLE CHECK: g_1 = (1 6 4 3 a_1 ... a_n) is a (4+n)-cycle, hence a cycle in the sense of Lemma 11.2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** INTERSECTION: a_1 ∈ B (by definition of B as the block containing a_1) and a_1 ∈ supp(g_1). Thus supp(g_1) ∩ B ≠ ∅.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** APPLICATION OF LEMMA 11.2: Since g_1 is a cycle with g_1(B) = B and supp(g_1) ∩ B ≠ ∅, by Lemma 11.2, supp(g_1) ⊆ B. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

