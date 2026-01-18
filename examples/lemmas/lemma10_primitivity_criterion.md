# Proof Export

## Node 1

**Statement:** Let G <= S_n be transitive. The following are equivalent: (1) G is primitive, (2) G preserves no non-trivial partition of {1,...,n}, (3) For any alpha, the stabilizer G_alpha is a maximal subgroup of G.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: We prove (1)⟺(2)⟺(3) by showing the cycle (1)⟹(2)⟹(3)⟹(1). Each implication uses the block-stabilizer correspondence.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** IMPLICATION (1)⟹(2): Suppose G is primitive. By definition (Primitive_Action), the only block systems are trivial. Hence G preserves no non-trivial partition.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** IMPLICATION (2)⟹(3) SETUP: Suppose G preserves no non-trivial partition. Fix α ∈ Ω. We must show G_α is maximal in G. Let H be a subgroup with G_α ≤ H ≤ G. We show H = G_α or H = G.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** IMPLICATION (2)⟹(3) BLOCK CONSTRUCTION: Define B = H·α = {h(α) : h ∈ H}, the H-orbit of α. Claim: B is a block for G.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** IMPLICATION (2)⟹(3) BLOCK PROOF: Let g ∈ G. Either g(B) ∩ B = ∅, or there exist h₁, h₂ ∈ H with g·h₁(α) = h₂(α). Then h₂⁻¹gh₁ ∈ G_α ≤ H, so g ∈ H. Thus g(B) = H·g(α) = H·α = B. Hence B is a block.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** IMPLICATION (2)⟹(3) CONCLUSION: Since G preserves no non-trivial partition, B is trivial. Case B={α}: Then H·α={α}, so H stabilizes α, hence H ≤ G_α. With G_α ≤ H, we get H = G_α. Case B=Ω: By Block_Stabilizer_Correspondence, there is a bijection K ↔ K·α between subgroups G_α ≤ K ≤ G and blocks containing α. Since G·α = Ω (G transitive) and H·α = Ω, bijectivity gives H = G. Hence G_α is maximal.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** IMPLICATION (3)⟹(1) SETUP: Suppose for all α, G_α is maximal in G. Let B be a block with |B| > 1. Pick α ∈ B. We show B = Ω (so only trivial blocks exist).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.8

**Statement:** IMPLICATION (3)⟹(1) STABILIZER CHAIN: Let G_B = {g ∈ G : g(B) = B}. Since α ∈ B, we have G_α ≤ G_B. Since |B| > 1, pick β ∈ B with β ≠ α. By transitivity, there exists g ∈ G with g(α) = β. Since B is a block and g(α) = β ∈ B, we have g(B) = B, so g ∈ G_B. But g(α) = β ≠ α, so g ∉ G_α. Thus G_α < G_B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.9

**Statement:** IMPLICATION (3)⟹(1) CONCLUSION: Since G_α is maximal and G_α < G_B ≤ G, we must have G_B = G. Thus every g ∈ G fixes B setwise, so B = Ω (since G is transitive). Hence G is primitive. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

