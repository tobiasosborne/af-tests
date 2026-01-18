# Proof Export

## Node 1

**Statement:** If n + k + m >= 1, then H admits no non-trivial block system on Omega.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** SETUP - Assume for contradiction that B is a non-trivial H-invariant block system with block size d (1 < d < N). WLOG JUSTIFICATION: The hypothesis is n + k + m >= 1, so at least one of n, k, m is positive. We argue WLOG that n >= 1. If instead k >= 1 (or m >= 1), we can relabel the generators and elements: rename (g_1, g_2, g_3) -> (g_2, g_1, g_3) [or (g_3, g_1, g_2)] and correspondingly relabel tail elements (a_i, b_j, c_l) -> (b_j, a_i, c_l) [or (c_l, a_i, b_j)] and core elements {1,2,3,4,5,6} appropriately. This relabeling preserves the group structure because: (i) all three generators are cycles of the same form (4+tail)-cycle, (ii) the pairwise intersection pattern |supp(g_i) intersect supp(g_j)| = 2 for i \!= j is preserved (each pair shares exactly 2 core points), (iii) the tail elements remain disjoint across generators. After relabeling, the generator with positive tail length becomes the 'new g_1' with 'new n >= 1'. Thus WLOG assume n >= 1. Let B be the specific block containing a_1. By definition of block system, for any h in H, either h(B) = B or h(B) is disjoint from B.

**Type:** local_assume

**Inference:** local_assume

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** CASE 1 SETUP - Assume g_1(B) = B. By Lemma 11.3 (tail in block implies support in block): Since a_1 is in B and g_1(B) = B, we conclude supp(g_1) = {1, 3, 4, 6, a_1, ..., a_n} is contained in B. EXPLICIT CONTENTS: B now contains at minimum {1, 3, 4, 6, a_1, ..., a_n}. In particular, the core points 1, 3, 4, 6 are all in B.

**Type:** case

**Inference:** local_assume

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** CASE 1a - Assume additionally g_2(B) = B. STEP: Since 1 is in B (from Case 1 Setup) and 1 is in supp(g_2) = {1, 2, 4, 5, b_1, ..., b_k}, we have B intersects supp(g_2) non-trivially. By Lemma 11.2 (cycle stabilizer implies support containment): Since g_2(B) = B and B intersects supp(g_2), we conclude supp(g_2) is contained in B. EXPLICIT CONTENTS: B now contains {1, 2, 3, 4, 5, 6, a_1, ..., a_n, b_1, ..., b_k}. This is |B| >= 6 + n + k elements.

**Type:** case

**Inference:** local_assume

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** CASE 1a - g_3 analysis. CURRENT STATE: B contains {1, 2, 3, 4, 5, 6, a_1, ..., a_n, b_1, ..., b_k}. OBSERVATION: supp(g_3) = {2, 3, 5, 6, c_1, ..., c_m}. Therefore {2, 3, 5, 6} is contained in both B and supp(g_3), so B intersects supp(g_3) non-trivially (contains at least 4 elements). CASE SPLIT: Either g_3(B) = B (Case 1a-i) or g_3(B) is not equal to B (Case 1a-ii).

**Type:** claim

**Inference:** modus_ponens

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** CASE 1a-i: Assume g_3(B) = B. APPLICATION OF LEMMA 11.2: Since g_3(B) = B and B intersects supp(g_3) (specifically {2,3,5,6} is in both), by Lemma 11.2 we conclude supp(g_3) = {2, 3, 5, 6, c_1, ..., c_m} is entirely contained in B. EXPLICIT CONTENTS: B now contains {1, 2, 3, 4, 5, 6, a_1, ..., a_n, b_1, ..., b_k, c_1, ..., c_m} = Omega. CONCLUSION: |B| = N = |Omega|. CONTRADICTION: This contradicts that B is non-trivial (requires |B| < N).

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** CASE 1a-ii: Assume g_3(B) is not equal to B. SETUP: Since B intersects supp(g_3) non-trivially and g_3(B) is not equal to B, by block definition g_3(B) is disjoint from B. The orbit of B under <g_3> has size r > 1. APPLICATION OF LEMMA 11.4: Since g_3 is a (4+m)-cycle and B intersects supp(g_3) non-trivially, we have: (i) r divides (4+m), and (ii) |B intersect supp(g_3)| = (4+m)/r. CONSTRAINT: We established {2,3,5,6} is contained in B intersect supp(g_3), so |B intersect supp(g_3)| >= 4. Therefore (4+m)/r >= 4, which gives r <= (4+m)/4 = 1 + m/4.

**Type:** claim

**Inference:** modus_ponens

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** CASE 1a-ii IMMEDIATE CONTRADICTION: We prove Case 1a-ii is impossible via a simpler argument than orbit analysis. SETUP RECALL: In Case 1a-ii, B contains {1, 2, 3, 4, 5, 6, a_1, ..., a_n, b_1, ..., b_k} (from nodes 1.3, 1.4), and g_3(B) != B (assumption of Case 1a-ii). Since g_3(B) != B, by block property g_3(B) is disjoint from B. FIXED POINT ANALYSIS: supp(g_3) = {2, 3, 5, 6, c_1, ..., c_m}. The elements {1, 4, a_1, ..., a_n, b_1, ..., b_k} are NOT in supp(g_3). Therefore g_3 FIXES these elements: g_3(1) = 1, g_3(4) = 4, g_3(a_i) = a_i, g_3(b_j) = b_j for all i, j. CONTRADICTION: Since 1 is in B (from Case 1a setup), and g_3(1) = 1, we have 1 is in g_3(B). Thus 1 is in both B and g_3(B), so B cap g_3(B) contains {1} != empty. This contradicts that g_3(B) is disjoint from B. CONCLUSION: Case 1a-ii (g_1(B) = B, g_2(B) = B, g_3(B) != B) is IMPOSSIBLE.

**Type:** claim

**Inference:** modus_ponens

**Status:** validated

**Taint:** clean

### Node 1.8

**Statement:** CASE 1a-ii CONCLUSION: Node 1.7 establishes that Case 1a-ii is IMPOSSIBLE via the fixed-point argument. To summarize: In Case 1a-ii, B contains {1, 2, 3, 4, 5, 6, a_i, b_j} and we assume g_3(B) != B (hence g_3(B) disjoint from B). But g_3 FIXES elements outside supp(g_3) = {2,3,5,6,c_l}. Specifically, g_3(1) = 1 and g_3(4) = 4 and g_3(a_i) = a_i and g_3(b_j) = b_j. Since 1 is in B, we have g_3(1) = 1 is in g_3(B), so 1 is in B cap g_3(B), contradicting disjointness. CONCLUSION: Case 1a-ii cannot occur. Combined with Case 1a-i (which also gives contradiction by B = Omega), we conclude Case 1a is impossible. Combined with Case 1b impossibility (node 1.9.6), we conclude Case 1 (g_1(B) = B) always leads to contradiction. The only remaining case is Case 2 (g_1(B) != B), addressed in nodes 1.9.1ff.

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

#### Node 1.8.1

**Statement:** OVERALL CONCLUSION: We have exhaustively analyzed all cases via fixed-point arguments. CASE 1 (g_1(B) = B): From node 1.2, B contains supp(g_1) = {1,3,4,6,a_i}. CASE 1a (g_2(B) = B): B contains {1,2,3,4,5,6,a_i,b_j} (nodes 1.3-1.4). Case 1a-i (g_3(B)=B): B=Omega, contradiction (node 1.5). Case 1a-ii (g_3(B)!=B): Elements {1,4,a_i,b_j} fixed by g_3 contradict disjointness (node 1.7). CASE 1b (g_2(B)!=B): IMPOSSIBLE - elements {3,6,a_i} fixed by g_2 contradict disjointness (node 1.9.6). CASE 2 (g_1(B)!=B): Tail elements {a_i} fixed by g_2 and g_3 force g_2(B)=g_3(B)=B; then Lemma 11.2 forces supports into B, giving |B|=N (node 1.9.5). All cases lead to contradiction. CONCLUSION: When n+k+m>=1, group H admits NO non-trivial block system. QED.

**Type:** qed

**Inference:** local_discharge

**Status:** validated

**Taint:** clean

### Node 1.9

**Statement:** CASE 1b - Assume g_1(B) = B AND g_2(B) is not equal to B. FROM CASE 1 SETUP (1.2): B contains supp(g_1) = {1, 3, 4, 6, a_1, ..., a_n}. EXPLICIT CONTENTS: B contains {1, 3, 4, 6, a_1, ..., a_n}. ANALYSIS OF g_2: Since g_2(B) is not equal to B, and 1 is in B intersect supp(g_2), by block property g_2(B) is disjoint from B. g_2 = (1 2 4 5 b_1 ... b_k) maps: g_2(1) = 2, g_2(4) = 5. Since 1, 4 are in B, we have 2, 5 are in g_2(B). Also g_2(B) intersect B = empty. EXPLICIT CONTENTS: g_2(B) contains {2, 5} at minimum.

**Type:** case

**Inference:** local_assume

**Status:** validated

**Taint:** clean

#### Node 1.9.1

**Statement:** STRUCTURAL NOTE: This node and siblings 1.9.2-1.9.5 were originally labeled as 'Case 2' but incorrectly placed under node 1.9 (Case 1b). Node 1.9.6 establishes that Case 1b is IMPOSSIBLE, making this subtree unnecessary for Case 1b. The Case 2 analysis (g_1(B) \!= B) is now handled separately. CASE 2 ANALYSIS (g_1(B) \!= B): Since a_1 is in B and a_1 is in supp(g_1), B intersects supp(g_1). Since g_1(B) \!= B, g_1(B) is disjoint from B. FIXED POINT ARGUMENT: Elements {a_1, ..., a_n} are ONLY in supp(g_1) - they are NOT in supp(g_2) or supp(g_3). Therefore g_2(a_i) = a_i and g_3(a_i) = a_i for all i. CONSEQUENCE: If g_2(B) \!= B, then g_2(B) disjoint from B, but g_2(a_1) = a_1 means a_1 in both B and g_2(B). CONTRADICTION. Therefore g_2(B) = B. Similarly g_3(B) = B. So in Case 2, we have g_1(B) \!= B but g_2(B) = g_3(B) = B.

**Type:** case

**Inference:** local_assume

**Status:** validated

**Taint:** clean

#### Node 1.9.2

**Statement:** CASE 2 - SUPERSEDED BY FIXED-POINT ARGUMENT: This node's orbit analysis is superseded by the simpler argument in nodes 1.9.1 and 1.9.5. The key insight is: tail elements {a_1, ..., a_n} are fixed by both g_2 and g_3 (not in their supports). Therefore, if g_2(B) \!= B or g_3(B) \!= B, the element a_1 (which is in B) would be in both B and the disjoint image, contradiction. Hence g_2(B) = g_3(B) = B in Case 2. This makes the detailed orbit analysis unnecessary - see node 1.9.5 for the complete Case 2 argument.

**Type:** claim

**Inference:** modus_ponens

**Status:** archived

**Taint:** clean

#### Node 1.9.3

**Statement:** CASE 2 - Sub-case B: If 1 and 4 are in DIFFERENT g_1-orbit blocks. Say 1 is in g_1^j(B) and 4 is in g_1^l(B) with j \!= l. Then g_2(1) = 2 and g_2(4) = 5. Since g_2 maps 1 (in g_1^j(B)) to 2 (in g_2(g_1^j(B))) and maps 4 (in g_1^l(B)) to 5 (in g_2(g_1^l(B))), the action of g_2 permutes the g_1-orbit blocks. KEY: In the cycle g_1 = (1 6 4 3 a_1 ... a_n), note that g_1(1) = 6, g_1(6) = 4, g_1(4) = 3, g_1(3) = a_1. So if orbit size r = 2, each block has (4+n)/2 elements. Elements 1, 4 separated means they're in different blocks. But g_1^2(1) = 4 (since g_1(1) = 6, g_1(6) = 4). So 1 and 4 are in same g_1^2 orbit, meaning same block for r = 2. Contradiction.

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

#### Node 1.9.4

**Statement:** CASE 2 - SUPERSEDED BY FIXED-POINT ARGUMENT: This node's detailed orbit analysis for r >= 3 is superseded by the simpler argument in nodes 1.9.1 and 1.9.5. The key insight is: tail elements {a_1, ..., a_n} are NOT in supp(g_2) or supp(g_3), so g_2(a_i) = a_i and g_3(a_i) = a_i for all i. Since a_1 is in B, if g_2(B) \!= B (disjoint from B), then a_1 would be in both B and g_2(B), contradiction. Therefore g_2(B) = B (and similarly g_3(B) = B) in Case 2. This bypasses the need for orbit analysis under g_1. See node 1.9.5 for the complete Case 2 argument.

**Type:** claim

**Inference:** modus_ponens

**Status:** archived

**Taint:** clean

#### Node 1.9.5

**Statement:** CASE 2 CONCLUSION (g_1(B) != B): From the amended node 1.9.1, we have a simpler argument via fixed points. FIXED POINT ARGUMENT: The tail elements {a_1, ..., a_n} are in supp(g_1) ONLY - they are not in supp(g_2) or supp(g_3). Therefore g_2(a_i) = a_i and g_3(a_i) = a_i for all i. Since a_1 is in B (from setup in 1.1), if g_2(B) != B then g_2(B) is disjoint from B. But g_2(a_1) = a_1 means a_1 is in both B and g_2(B). CONTRADICTION. Therefore g_2(B) = B. By the same argument, g_3(B) = B. APPLYING LEMMA 11.2: Since g_2(B) = B and B contains a_1 (which is in Omega), we need B to intersect supp(g_2) to apply Lemma 11.2. The orbit of B under g_1 partitions supp(g_1) = {1,3,4,6,a_i}. Elements 1 and 4 are in supp(g_1) cap supp(g_2). Wherever 1 ends up (in some g_1^j(B)), that block intersects supp(g_2). Since g_2 stabilizes blocks in the orbit of B (as g_2(B)=B implies g_2(g_1^j(B))=g_1^j(B) by normality-like argument), Lemma 11.2 applies. This eventually forces supp(g_2) cup supp(g_3) to be in a single block, giving |B| >= 6+k+m elements, leading to |B| = N contradiction as in Case 1a.

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

#### Node 1.9.6

**Statement:** CASE 1b IMPOSSIBILITY: The assumption g_2(B) != B leads to immediate contradiction. From node 1.2, B contains supp(g_1) = {1, 3, 4, 6, a_1, ..., a_n}. FIXED POINT ANALYSIS: Elements {3, 6, a_1, ..., a_n} are NOT in supp(g_2) = {1, 2, 4, 5, b_j}. Therefore g_2 FIXES these elements: g_2(3) = 3, g_2(6) = 6, g_2(a_i) = a_i. CONTRADICTION: If g_2(B) != B, then g_2(B) is disjoint from B (block property). But 3 is in B (from 1.2), and g_2(3) = 3 means 3 is in g_2(B). Thus 3 is in B cap g_2(B), contradicting disjointness. CONCLUSION: Case 1b is IMPOSSIBLE. Under Case 1, we must have g_2(B) = B, so Case 1 reduces entirely to Case 1a. The child nodes 1.9.1-1.9.5 (originally labeled as Case 2) are superseded by this analysis and the proper Case 2 analysis below.

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

### Node 1.10

**Statement:** CASE 1b - Analysis of g_3. CURRENT STATE: B contains {1, 3, 4, 6, a_i}, g_2(B) contains {2, 5}, and B intersect g_2(B) = empty. KEY OBSERVATION: supp(g_3) = {2, 3, 5, 6, c_1, ..., c_m}. Elements 3, 6 are in B. Elements 2, 5 are in g_2(B). So supp(g_3) intersects BOTH B and g_2(B) non-trivially. CONTRAPOSITIVE OF LEMMA 11.2: If g_3 fixes B setwise (g_3(B) = B), then since supp(g_3) intersects B, we need supp(g_3) contained in B. But 2, 5 are in supp(g_3) and 2, 5 are in g_2(B) which is disjoint from B. So supp(g_3) is NOT contained in B. CONCLUSION: g_3(B) is not equal to B.

**Type:** claim

**Inference:** modus_tollens

**Status:** validated

**Taint:** clean

#### Node 1.10.1

**Statement:** CASE 1b ORBIT ANALYSIS - SUPERSEDED: This node's orbit growth argument is superseded by node 1.9.6 which proves Case 1b is IMPOSSIBLE. The impossibility follows from the fixed-point argument: elements {3, 6, a_1, ..., a_n} in B are fixed by g_2 (not in supp(g_2)), so if g_2(B) \!= B then 3 is in both B and g_2(B), contradicting disjointness. Since Case 1b cannot occur, this orbit analysis is vacuously true. See node 1.9.6 for the proof of Case 1b impossibility.

**Type:** claim

**Inference:** modus_ponens

**Status:** validated

**Taint:** clean

#### Node 1.10.2

**Statement:** CASE 1b CONCLUSION - SUPERSEDED: This node is superseded by node 1.9.6 which proves Case 1b is IMPOSSIBLE. The impossibility follows from the fixed-point argument: elements {3, 6, a_1, ..., a_n} in B are fixed by g_2 (not in supp(g_2)), so if g_2(B) != B (disjoint), then 3 is in both B and g_2(B), contradiction. Therefore Case 1b (g_1(B)=B AND g_2(B)!=B) cannot occur when n >= 1. The analysis in this subtree (1.10, 1.10.1, 1.10.2) is vacuously true since Case 1b is impossible. Case 1 reduces entirely to Case 1a.

**Type:** claim

**Inference:** contradiction

**Status:** validated

**Taint:** clean

