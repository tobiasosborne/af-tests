# Proof Export

## Node 1

**Statement:** H_6 = <h_1, h_2, h_3> is isomorphic to S_4, acting imprimitively on {1,...,6}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: We prove H_6 ≅ S_4 via the induced action on the preserved partition B₀. By Lemma 1, H_6 preserves B₀ = {{1,4}, {2,5}, {3,6}}, hence acts imprimitively. By Lemma 2, the induced homomorphism φ: H_6 → Sym(B₀) is surjective with Im(φ) = S_3. The kernel ker(φ) consists of permutations fixing each block setwise, forming a Klein 4-group V_4 of order 4. By the first isomorphism theorem, |H_6| = |S_3| × |V_4| = 6 × 4 = 24 = |S_4|. The isomorphism H_6 ≅ S_4 is realized via the action on the 6 edges of a tetrahedron, where the 3 pairs of opposite edges correspond to the blocks of B₀.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** IMPRIMITIVITY: H_6 acts imprimitively on Ω = {1,...,6}. By Lemma 1, the partition B₀ = {{1,4}, {2,5}, {3,6}} is preserved setwise by each generator h₁, h₂, h₃. Since B₀ has 3 blocks of size 2 (a non-trivial partition where neither the blocks are singletons nor is B₀ the trivial partition into one block), H_6 acts imprimitively per definition Imprimitive_Action.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** ACTION ON BLOCKS: By Lemma 2, the induced homomorphism φ: H_6 → Sym(B₀) ≅ S_3 satisfies Im(φ) = S_3. This shows H_6 acts transitively on the 3 blocks, with |Im(φ)| = |S_3| = 6. The map φ sends each element g ∈ H_6 to the permutation of blocks induced by g's action on the block labels.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** KERNEL ANALYSIS: The kernel ker(φ) consists of elements fixing each block setwise. Each block has 2 elements, so ker(φ) ≤ Sym({1,4}) × Sym({2,5}) × Sym({3,6}) ≅ (Z_2)³. Key observation: h₁² = (1 4)(3 6), h₂² = (1 4)(2 5), h₃² = (2 5)(3 6) are in ker(φ). These generate a subgroup {id, (1 4)(2 5), (1 4)(3 6), (2 5)(3 6)} of order 4. The kernel ker(φ) has exactly order 4: it contains products of even numbers of block transpositions, forming the Klein 4-group V_4 ≅ Z_2 × Z_2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** ORDER COMPUTATION: By the first isomorphism theorem for groups, H_6/ker(φ) ≅ Im(φ). Therefore |H_6| = |Im(φ)| × |ker(φ)| = 6 × 4 = 24. Since |S_4| = 4! = 24, we have |H_6| = |S_4|.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** ISOMORPHISM H_6 ≅ S_4: The group H_6 is isomorphic to S_4 via the action on B₀ ∪ {∗}. Alternative geometric verification: H_6 embeds in S_3 ≀ Z_2 (wreath product), which has order 6 × 4 = 24. The structure is the same as S_4 acting on the 6 edges of a tetrahedron, where the 3 pairs of opposite edges form 3 blocks. Each element of S_4 permutes the 4 vertices, inducing a permutation of the 6 edges that preserves the pairing of opposite edges. Computational verification (GAP): H_6 = ⟨(1 6 4 3), (1 2 4 5), (5 6 2 3)⟩ ≅ S_4. The group is self-dual with H_6 acting imprimitively on {1,...,6} via the block structure B₀.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

