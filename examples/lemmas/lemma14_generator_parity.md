# Proof Export

## Node 1

**Statement:** sign(g_1) = (-1)^{n+3}, sign(g_2) = (-1)^{k+3}, sign(g_3) = (-1)^{m+3}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** PROOF OVERVIEW: Each generator g_i is a single cycle. We apply Lemma 13 (validated) to compute the sign of each generator based on its cycle length.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** SIGN OF g_1: The generator g_1 = (1 4 a_1 ... a_n 2 5) is a cycle of length l = 4 + n (4 core elements plus n tail elements). By Lemma 13, sign(g_1) = (-1)^{l-1} = (-1)^{(4+n)-1} = (-1)^{3+n} = (-1)^{n+3}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** SIGN OF g_2: The generator g_2 = (2 5 b_1 ... b_k 3 6) is a cycle of length l = 4 + k (4 core elements plus k tail elements). By Lemma 13, sign(g_2) = (-1)^{l-1} = (-1)^{(4+k)-1} = (-1)^{3+k} = (-1)^{k+3}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** SIGN OF g_3: The generator g_3 = (3 6 c_1 ... c_m 1 4) is a cycle of length l = 4 + m (4 core elements plus m tail elements). By Lemma 13, sign(g_3) = (-1)^{l-1} = (-1)^{(4+m)-1} = (-1)^{3+m} = (-1)^{m+3}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** CONCLUSION: By nodes 1.2, 1.3, and 1.4, we have established: sign(g_1) = (-1)^{n+3}, sign(g_2) = (-1)^{k+3}, sign(g_3) = (-1)^{m+3}. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

