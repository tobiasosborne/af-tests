# Proof Export

## Node 1

**Statement:** Let g_1 = (1 6 4 3 7) and g_3 = (5 6 2 3) in S_7. Then [g_1, g_3] = (1 5 6)(2 3 4).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: We compute [g_1, g_3] = g_1^{-1} g_3^{-1} g_1 g_3 by tracing all 7 elements of {1,2,3,4,5,6,7} through the composition. Using the convention [σ,τ](x) = σ^{-1}(τ^{-1}(σ(τ(x)))) from definition Commutator, we trace each element and identify the cycle decomposition.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** PART 1 - INVERSE VERIFICATION (citing Cycle_Inverse): By Cycle_Inverse, reversing (1 6 4 3 7) gives (7 3 4 6 1), standard form g_1^{-1} = (1 7 3 4 6). By Cycle_Inverse, reversing (5 6 2 3) gives (3 2 6 5), standard form g_3^{-1} = (5 3 2 6). Verification: g_1 maps 1→6, g_1^{-1} maps 6→1. g_3 maps 5→6, g_3^{-1} maps 6→5. Correct.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** PART 2 - ACTION TABLES: g_1 = (1 6 4 3 7): 1→6, 6→4, 4→3, 3→7, 7→1; fixes 2, 5. g_3 = (5 6 2 3): 5→6, 6→2, 2→3, 3→5; fixes 1, 4, 7. g_1^{-1} = (1 7 3 4 6): 1→7, 7→3, 3→4, 4→6, 6→1; fixes 2, 5. g_3^{-1} = (5 3 2 6): 5→3, 3→2, 2→6, 6→5; fixes 1, 4, 7.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** TRACE x=1: g_3(1)=1 (1 is fixed by g_3) → g_1(1)=6 → g_3^{-1}(6)=5 → g_1^{-1}(5)=5 (5 is fixed by g_1^{-1}). Therefore 1 ↦ 5.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** TRACE x=2: g_3(2)=3 → g_1(3)=7 → g_3^{-1}(7)=7 (7 is fixed by g_3^{-1}) → g_1^{-1}(7)=3. Therefore 2 ↦ 3.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** TRACE x=3: g_3(3)=5 → g_1(5)=5 (5 is fixed by g_1) → g_3^{-1}(5)=3 → g_1^{-1}(3)=4. Therefore 3 ↦ 4.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** TRACE x=4: g_3(4)=4 (4 is fixed by g_3) → g_1(4)=3 → g_3^{-1}(3)=2 → g_1^{-1}(2)=2 (2 is fixed by g_1^{-1}). Therefore 4 ↦ 2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.8

**Statement:** TRACE x=5: g_3(5)=6 → g_1(6)=4 → g_3^{-1}(4)=4 (4 is fixed by g_3^{-1}) → g_1^{-1}(4)=6. Therefore 5 ↦ 6.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.9

**Statement:** TRACE x=6: g_3(6)=2 → g_1(2)=2 (2 is fixed by g_1) → g_3^{-1}(2)=6 → g_1^{-1}(6)=1. Therefore 6 ↦ 1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.10

**Statement:** TRACE x=7: g_3(7)=7 (7 is fixed by g_3) → g_1(7)=1 → g_3^{-1}(1)=1 (1 is fixed by g_3^{-1}) → g_1^{-1}(1)=7. Therefore 7 ↦ 7 (FIXED POINT).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.10.1

**Statement:** PART 3 - ORBIT ANALYSIS AND CONCLUSION: Complete mapping: 1→5, 2→3, 3→4, 4→2, 5→6, 6→1, 7→7. Orbit 1: 1→5→6→1 forms 3-cycle (1 5 6). Orbit 2: 2→3→4→2 forms 3-cycle (2 3 4). Orbit 3: 7→7 is fixed. RESULT: [g_1, g_3] = (1 5 6)(2 3 4). QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

