# Proof Export

## Node 1

**Statement:** If n + k + m >= 1, then H acts primitively on Omega.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** PROOF STRUCTURE: This is a direct application of three validated lemmas. We establish (i) transitivity via Lemma 5, (ii) absence of non-trivial block systems via Lemma 11.5, then (iii) conclude primitivity via the criterion in Lemma 10.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** TRANSITIVITY (Lemma 5): By Lemma 5, the group H = <g_1, g_2, g_3> acts transitively on Omega. This was established by showing the support graph of the generators is connected, allowing any element to be mapped to any other via compositions of generators.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** NO NON-TRIVIAL BLOCK SYSTEM (Lemma 11.5): By Lemma 11.5 (validated via fixed-point arguments), when n + k + m >= 1, the group H admits no non-trivial block system on Omega. The proof used fixed-point arguments: if an element x is fixed by generator g and lies in block B, then x in g(B), which forces g(B) = B (not disjoint), eventually showing any block B must equal all of Omega.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** PRIMITIVITY CRITERION (Lemma 10): By Lemma 10, for a transitive group G on set X: G is primitive if and only if G preserves no non-trivial partition of X. Since H is transitive on Omega (established in node 1.2 via Lemma 5) and H preserves no non-trivial partition of Omega (established in node 1.3 via Lemma 11.5), we conclude by Lemma 10 implication (2) => (1) that H acts primitively on Omega. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

