# Proof Export

## Node 1

**Statement:** Let G <= S_n with G >= A_n. Then: G = A_n iff G <= A_n iff all generators of G are even. G = S_n iff G contains an odd permutation.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** PROOF OVERVIEW: We use the index-2 property of A_n in S_n. Since [S_n : A_n] = 2, any subgroup G with A_n ≤ G ≤ S_n must be either A_n or S_n. We then characterize which case holds based on the parity of the generators.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** INDEX-2 DICHOTOMY: Since [S_n : A_n] = 2, the subgroup A_n has exactly two cosets in S_n: the coset A_n (even permutations) and the coset S_n \ A_n (odd permutations). By Lagrange's theorem, any subgroup G with A_n ≤ G ≤ S_n has index [S_n : G] dividing [S_n : A_n] = 2. Thus [S_n : G] ∈ {1, 2}, which means G = S_n or G = A_n.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** CHARACTERIZATION OF G = A_n: G = A_n ⟺ G ≤ A_n (since A_n ≤ G by hypothesis) ⟺ all elements of G are even permutations ⟺ sign(g) = +1 for all g ∈ G ⟺ sign(g) = +1 for all generators g of G (since sign is a homomorphism: if generators map to +1, all products do too).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** CHARACTERIZATION OF G = S_n: G = S_n ⟺ G ≠ A_n (by node 1.2, these are the only options) ⟺ G ⊈ A_n ⟺ G contains some element that is not in A_n ⟺ G contains an odd permutation.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** CONCLUSION: Combining nodes 1.2, 1.3, and 1.4: For G with A_n <= G <= S_n, we have G = A_n iff all generators are even (node 1.3), and G = S_n iff G contains an odd permutation (node 1.4). The dichotomy follows from the index-2 property (node 1.2). QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

