# Proof Export

## Node 1

**Statement:** An l-cycle in S_n has sign (-1)^{l-1}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** PROOF OVERVIEW: We prove that an l-cycle has sign (-1)^{l-1} by (1) decomposing the cycle into transpositions, (2) counting the transpositions, and (3) applying the sign homomorphism.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** CYCLE DECOMPOSITION: An l-cycle (a_1 a_2 ... a_l) can be written as a product of transpositions: (a_1 a_2 ... a_l) = (a_1 a_l)(a_1 a_{l-1})(a_1 a_{l-2})...(a_1 a_3)(a_1 a_2). VERIFICATION: Apply the right-hand side to each a_i. For a_1: (a_1 a_2) sends a_1 -> a_2, subsequent transpositions fix a_2, so a_1 -> a_2. For a_j (1 < j < l): (a_1 a_j) sends a_j -> a_1, then (a_1 a_{j+1}) sends a_1 -> a_{j+1}, so a_j -> a_{j+1}. For a_l: (a_1 a_l) sends a_l -> a_1, and (a_1 a_2)...(a_1 a_{l-1}) fix a_1, so a_l -> a_1. This matches the l-cycle definition.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** TRANSPOSITION COUNT: The decomposition (a_1 a_l)(a_1 a_{l-1})...(a_1 a_2) contains exactly l-1 transpositions. Explicitly: the factors are (a_1 a_l), (a_1 a_{l-1}), ..., (a_1 a_3), (a_1 a_2), which are indexed by the second element running from l down to 2, giving l-1 terms.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** SIGN CALCULATION: By the sign homomorphism property, sign(sigma tau) = sign(sigma) * sign(tau). Each transposition has sign -1. Therefore: sign((a_1 a_2 ... a_l)) = sign((a_1 a_l)) * sign((a_1 a_{l-1})) * ... * sign((a_1 a_2)) = (-1) * (-1) * ... * (-1) [l-1 times] = (-1)^{l-1}. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

