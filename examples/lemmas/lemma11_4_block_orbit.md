# Proof Export

## Node 1

**Statement:** Let sigma in S_n be an l-cycle and B a sigma-invariant block system with block size d. Let B in B with B intersect supp(sigma) nonempty. Let r be the size of the <sigma>-orbit of B in B. Then r divides l and |B intersect supp(sigma)| = l/r.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: The cycle σ permutes blocks. The orbit size r divides ℓ = |⟨σ⟩|, and supp(σ) is evenly distributed across the r blocks in the orbit.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** BLOCK PERMUTATION: Since B is σ-invariant, σ induces a permutation on B. For any block B ∈ B, σ(B) is also a block in B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** ORBIT SIZE DIVIDES: The ⟨σ⟩-orbit of B has size r. By Orbit-Stabilizer theorem applied to ⟨σ⟩ acting on B, r divides |⟨σ⟩| = ℓ.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** SUPPORT PARTITION: supp(σ) is the single orbit of σ on the domain (since σ is a cycle). The blocks that intersect supp(σ) partition supp(σ).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** ORBIT BLOCKS: The r blocks in the ⟨σ⟩-orbit of B are exactly the blocks intersecting supp(σ). Forward: B ∩ supp(σ) ≠ ∅ and σ permutes supp(σ), so σⁱ(B) ∩ supp(σ) ≠ ∅ for all i. Converse: If B' ∩ supp(σ) ≠ ∅, pick x ∈ B' ∩ supp(σ) and y ∈ B ∩ supp(σ). Since σ acts transitively on supp(σ), σⁱ(y) = x for some i. Then x ∈ σⁱ(B) ∩ B', so B' = σⁱ(B) (blocks are disjoint or equal). Thus B' is in the orbit of B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** SYMMETRY ARGUMENT: σ acts transitively on {B, σ(B), ..., σ^{r-1}(B)} by cycling them. Since σ also cycles supp(σ), each block contains the same number of elements from supp(σ).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** COUNTING: The r blocks partition supp(σ) with |supp(σ)| = ℓ. By symmetry, each block contains ℓ/r elements of supp(σ). Thus |B ∩ supp(σ)| = ℓ/r. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

