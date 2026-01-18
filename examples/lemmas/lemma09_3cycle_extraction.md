# Proof Export

## Node 1

**Statement:** Let c_12 := (1 7 5)(2 4 6) and c_13 := (1 5 6)(2 3 4). Then: (1) c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7), and (2) (c_12 * c_13^{-1})^2 = (1 6 2).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: We compute c_12 * c_13^{-1} and then square it to extract a 3-cycle. The computation uses: c_12 = (1 7 5)(2 4 6) from Lemma 6, c_13 = (1 5 6)(2 3 4) from Lemma 7.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** PART 1 - INVERSE OF c_13 (citing Three_Cycle_Inverse): c_13 = (1 5 6)(2 3 4). Each 3-cycle inverts by reversing: (1 5 6)^{-1} = (1 6 5), (2 3 4)^{-1} = (2 4 3). Thus c_13^{-1} = (1 6 5)(2 4 3).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** PART 2 - ACTION TABLES: c_12 = (1 7 5)(2 4 6): 1→7, 7→5, 5→1, 2→4, 4→6, 6→2; fixes 3. c_13^{-1} = (1 6 5)(2 4 3): 1→6, 6→5, 5→1, 2→4, 4→3, 3→2; fixes 7.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** TRACE x=1: c_13^{-1}(1)=6 → c_12(6)=2. Therefore 1 ↦ 2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** TRACE x=2: c_13^{-1}(2)=4 → c_12(4)=6. Therefore 2 ↦ 6.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** TRACE x=3: c_13^{-1}(3)=2 → c_12(2)=4. Therefore 3 ↦ 4.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** TRACE x=4: c_13^{-1}(4)=3 → c_12(3)=3 (3 is fixed by c_12). Therefore 4 ↦ 3.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.8

**Statement:** TRACE x=5: c_13^{-1}(5)=1 → c_12(1)=7. Therefore 5 ↦ 7.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.9

**Statement:** TRACE x=6: c_13^{-1}(6)=5 → c_12(5)=1. Therefore 6 ↦ 1.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.10

**Statement:** TRACE x=7: c_13^{-1}(7)=7 (7 is fixed by c_13^{-1}) → c_12(7)=5. Therefore 7 ↦ 5.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.10.1

**Statement:** PART 3 - ORBIT ANALYSIS AND SQUARING: Complete mapping: 1→2, 2→6, 3→4, 4→3, 5→7, 6→1, 7→5. Orbits: (1 2 6), (3 4), (5 7). So c_12 * c_13^{-1} = (1 2 6)(3 4)(5 7). Squaring: (1 2 6)^2 = (1 6 2), (3 4)^2 = e, (5 7)^2 = e. By Disjoint_Cycle_Power: (c_12 * c_13^{-1})^2 = (1 6 2). QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

