# Proof Export

## Node 1

**Statement:** For all n, k, m >= 0, the group H = <g_1, g_2, g_3> acts transitively on Omega, where g_1 = (1 6 4 3 a_1 ... a_n), g_2 = (1 2 4 5 b_1 ... b_k), g_3 = (5 6 2 3 c_1 ... c_m).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** We prove transitivity of H on Ω by showing the support graph Γ is connected. By Definition (Graph_Connectivity), if Γ is connected, then H acts transitively on Ω. We proceed by: (1) identifying all edges in Γ from each generator, (2) showing the Core {1,2,3,4,5,6} forms a connected subgraph, (3) showing each tail vertex connects to the Core, and (4) concluding Γ is connected.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** Edges from g_1 = (1 6 4 3 a_1 ... a_n): Reading consecutive elements in the cycle, we get edges {1,6}, {6,4}, {4,3}, {3,a_1}, {a_1,a_2}, ..., {a_{n-1},a_n}, {a_n,1}. This forms a cycle of length 4+n in Γ connecting vertices 1, 6, 4, 3, and all a_i back to 1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** Edges from g_2 = (1 2 4 5 b_1 ... b_k): Reading consecutive elements in the cycle, we get edges {1,2}, {2,4}, {4,5}, {5,b_1}, {b_1,b_2}, ..., {b_{k-1},b_k}, {b_k,1}. This forms a cycle of length 4+k in Γ connecting vertices 1, 2, 4, 5, and all b_j back to 1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** Edges from g_3 = (5 6 2 3 c_1 ... c_m): Reading consecutive elements in the cycle, we get edges {5,6}, {6,2}, {2,3}, {3,c_1}, {c_1,c_2}, ..., {c_{m-1},c_m}, {c_m,5}. This forms a cycle of length 4+m in Γ connecting vertices 5, 6, 2, 3, and all c_ℓ back to 5.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** Core connectivity: The Core = {1,2,3,4,5,6} forms a connected subgraph of Γ. From g_1: edges {1,6}, {6,4}, {4,3}. From g_2: edges {1,2}, {2,4}, {4,5}. From g_3: edges {5,6}, {6,2}, {2,3}. Starting from vertex 1, we can reach: 6 via {1,6}; 4 via {6,4}; 3 via {4,3}; 2 via {1,2}; 5 via {4,5}. Thus all six Core vertices are connected.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** Tail vertices connect to Core: (i) Each a_i connects to Core: a_1 is adjacent to 3 via edge {3,a_1}, and the chain a_1-a_2-...-a_n-1 connects all a_i to both 3 and 1 in Core. (ii) Each b_j connects to Core: b_1 is adjacent to 5 via edge {5,b_1}, and the chain b_1-b_2-...-b_k-1 connects all b_j to both 5 and 1 in Core. (iii) Each c_ℓ connects to Core: c_1 is adjacent to 3 via edge {3,c_1}, and the chain c_1-c_2-...-c_m-5 connects all c_ℓ to both 3 and 5 in Core.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** Conclusion: The support graph Γ is connected. By nodes 1.2-1.4, we have identified all edges from generators g_1, g_2, g_3. By node 1.5, the Core forms a connected subgraph. By node 1.6, every tail vertex (a_i, b_j, c_ℓ) is connected to the Core via a path. Since every vertex in Ω = Core ∪ {a_i} ∪ {b_j} ∪ {c_ℓ} is connected to the Core, and the Core is connected, Γ is connected. By Definition (Graph_Connectivity), since Γ is connected, H = ⟨g_1, g_2, g_3⟩ acts transitively on Ω. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

