# Proof Export

## Node 1

**Statement:** Let g_2 = (1 2 4 5) and g_3 = (5 6 2 3) in S_7. Then [g_2, g_3] = (1 6 2)(3 5 4).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: We compute [g_2, g_3] = g_2^{-1} g_3^{-1} g_2 g_3 by tracing all 7 elements of {1,2,3,4,5,6,7} through the composition. Using the convention [σ,τ](x) = σ^{-1}(τ^{-1}(σ(τ(x)))) from definition Commutator, we trace each element and identify the cycle decomposition.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** PART 1 - INVERSE VERIFICATION (citing Cycle_Inverse): By Cycle_Inverse, reversing (1 2 4 5) gives (5 4 2 1), standard form g_2^{-1} = (1 5 4 2). By Cycle_Inverse, reversing (5 6 2 3) gives (3 2 6 5), standard form g_3^{-1} = (5 3 2 6). Verification: g_2 maps 1→2, g_2^{-1} maps 2→1. g_3 maps 5→6, g_3^{-1} maps 6→5. Correct.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** PART 2 - ACTION TABLES: g_2 = (1 2 4 5): 1→2, 2→4, 4→5, 5→1; fixes 3, 6, 7. g_3 = (5 6 2 3): 5→6, 6→2, 2→3, 3→5; fixes 1, 4, 7. g_2^{-1} = (1 5 4 2): 1→5, 5→4, 4→2, 2→1; fixes 3, 6, 7. g_3^{-1} = (5 3 2 6): 5→3, 3→2, 2→6, 6→5; fixes 1, 4, 7.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** TRACE x=1: g_3(1)=1 (1 is fixed by g_3) → g_2(1)=2 → g_3^{-1}(2)=6 → g_2^{-1}(6)=6 (6 is fixed by g_2^{-1}). Therefore 1 ↦ 6.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** TRACE x=2: g_3(2)=3 → g_2(3)=3 (3 is fixed by g_2) → g_3^{-1}(3)=2 → g_2^{-1}(2)=1. Therefore 2 ↦ 1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** TRACE x=3: g_3(3)=5 → g_2(5)=1 → g_3^{-1}(1)=1 (1 is fixed by g_3^{-1}) → g_2^{-1}(1)=5. Therefore 3 ↦ 5.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** TRACE x=4: g_3(4)=4 (4 is fixed by g_3) → g_2(4)=5 → g_3^{-1}(5)=3 → g_2^{-1}(3)=3 (3 is fixed by g_2^{-1}). Therefore 4 ↦ 3.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.8

**Statement:** TRACE x=5: g_3(5)=6 → g_2(6)=6 (6 is fixed by g_2) → g_3^{-1}(6)=5 → g_2^{-1}(5)=4. Therefore 5 ↦ 4.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.9

**Statement:** TRACE x=6: g_3(6)=2 → g_2(2)=4 → g_3^{-1}(4)=4 (4 is fixed by g_3^{-1}) → g_2^{-1}(4)=2. Therefore 6 ↦ 2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.10

**Statement:** TRACE x=7: g_3(7)=7 (7 is fixed by g_3) → g_2(7)=7 (7 is fixed by g_2) → g_3^{-1}(7)=7 (7 is fixed by g_3^{-1}) → g_2^{-1}(7)=7 (7 is fixed by g_2^{-1}). Therefore 7 ↦ 7 (FIXED POINT).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.10.1

**Statement:** PART 3 - ORBIT ANALYSIS AND CONCLUSION: Complete mapping: 1→6, 2→1, 3→5, 4→3, 5→4, 6→2, 7→7. Orbit 1: 1→6→2→1 forms 3-cycle (1 6 2). Orbit 2: 3→5→4→3 forms 3-cycle (3 5 4). Orbit 3: 7→7 is fixed. RESULT: [g_2, g_3] = (1 6 2)(3 5 4). QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

