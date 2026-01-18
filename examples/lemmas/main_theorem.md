# Proof Export

## Node 1

**Statement:** For n + k + m >= 1, let N = 6 + n + k + m and H = <g_1, g_2, g_3> where g_1 = (1 6 4 3 a_1...a_n), g_2 = (1 2 4 5 b_1...b_k), g_3 = (5 6 2 3 c_1...c_m). Then H = A_N if n,k,m are all odd, and H = S_N otherwise.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** PROOF OVERVIEW: We prove H = A_N or S_N by combining five validated lemmas and one admitted classical axiom: (1) transitivity (Lemma 5, validated), (2) primitivity (Lemma 11, validated), (3) 3-cycle existence (Lemma 9, validated), (4) Jordan's theorem (Lemma 12, admitted), (5) parity analysis (Lemma 14, validated), (6) A_N vs S_N criterion (Lemma 15, validated).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** STEP 1 - TRANSITIVITY (Lemma 5): By Lemma 5 (VALIDATED), the group H = <g_1, g_2, g_3> acts transitively on Omega. This was established via the connectivity of the support graph of the generators.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** STEP 2 - PRIMITIVITY (Lemma 11): By Lemma 11 (VALIDATED), when n + k + m >= 1, the group H acts primitively on Omega. The proof of Lemma 11 established that H preserves no non-trivial block system by analyzing block constraints imposed by the generators.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** STEP 3 - CONTAINS 3-CYCLE (Lemma 9): By Lemma 9 (VALIDATED), H contains the 3-cycle (1 6 2). This was extracted from commutators of the generators.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** STEP 4 - APPLY JORDAN (Lemma 12): By Lemma 12 (Jordan's Theorem, ADMITTED as classical axiom), since H is primitive (Step 2) and contains a 3-cycle (Step 3), we conclude H >= A_N. Note: N = 6 + n + k + m >= 7 when n + k + m >= 1, so N >= 5 as required by Jordan.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** STEP 5 - PARITY ANALYSIS (Lemma 14): By Lemma 14 (VALIDATED), sign(g_1) = (-1)^{n+3}, sign(g_2) = (-1)^{k+3}, sign(g_3) = (-1)^{m+3}. Arithmetic: (-1)^{x+3} = (-1)^x * (-1)^3 = -(-1)^x, so (-1)^{x+3} = +1 iff (-1)^x = -1 iff x is odd. Therefore: generator g_i is even iff its tail length is odd.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** STEP 6 - CONCLUSION (Lemma 15): By Lemma 15 (VALIDATED), since H >= A_N (Step 4): (Case 1) If n, k, m are all odd, then by Step 5 all generators are even, so H <= A_N, thus H = A_N. (Case 2) Otherwise, at least one of n, k, m is even, so by Step 5 H contains an odd generator, thus H contains an odd permutation and H = S_N. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

