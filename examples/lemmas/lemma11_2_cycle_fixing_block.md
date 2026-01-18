# Proof Export

## Node 1

**Statement:** Let sigma in S_n be a cycle with exactly one non-trivial orbit. Let B be a subset of {1,...,n} with sigma(B) = B. Then either supp(sigma) is contained in B or supp(sigma) is disjoint from B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: Let σ = (x_1 x_2 ... x_ℓ). We show: if supp(σ) ∩ B ≠ ∅, then supp(σ) ⊆ B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** SETUP: Assume supp(σ) ∩ B ≠ ∅. Pick x_i ∈ B ∩ supp(σ) for some i ∈ {1,...,ℓ}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** INDUCTION BASE: x_i ∈ B by assumption.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** INDUCTION STEP: Suppose x_j ∈ B for some j. Since σ(B) = B and x_j ∈ B, we have σ(x_j) = x_{j+1} ∈ B.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** INDUCTION CONCLUSION: By induction, x_{i+1}, x_{i+2}, ..., x_{i+ℓ-1} ∈ B. Since indices are mod ℓ, this covers all of {x_1, ..., x_ℓ} = supp(σ).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** CONCLUSION: supp(σ) ⊆ B. The contrapositive gives: supp(σ) ∩ B = ∅ or supp(σ) ⊆ B. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

