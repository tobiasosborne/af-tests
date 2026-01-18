# Proof Export

## Node 1

**Statement:** The only non-trivial block system for H_6 on {1,...,6} is B_0 = {{1,4}, {2,5}, {3,6}}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** OVERVIEW: Block sizes must divide 6, giving |B| ∈ {2, 3}. We enumerate all partitions and check H_6-invariance.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** CASE |B|=2: There are C(6,2)·C(4,2)·C(2,2)/3! = 15·6·1/6 = 15 partitions into 3 blocks of size 2.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** SIZE-2 ENUMERATION: The 15 partitions are: {{1,2},{3,4},{5,6}}, {{1,2},{3,5},{4,6}}, {{1,2},{3,6},{4,5}}, {{1,3},{2,4},{5,6}}, {{1,3},{2,5},{4,6}}, {{1,3},{2,6},{4,5}}, {{1,4},{2,3},{5,6}}, {{1,4},{2,5},{3,6}}, {{1,4},{2,6},{3,5}}, {{1,5},{2,3},{4,6}}, {{1,5},{2,4},{3,6}}, {{1,5},{2,6},{3,4}}, {{1,6},{2,3},{4,5}}, {{1,6},{2,4},{3,5}}, {{1,6},{2,5},{3,4}}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** SIZE-2 CHECK: h_1=(1 6 4 3) maps {1,4}→{6,3}={3,6}, {2,5}→{2,5}, {3,6}→{4,1}={1,4}. Only B_0={{1,4},{2,5},{3,6}} is invariant under all h_i (verified by Lemma 1).

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** CASE |B|=3: There are C(6,3)/2 = 20/2 = 10 partitions into 2 blocks of size 3.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.6

**Statement:** SIZE-3 ENUMERATION: The 10 partitions are: {{1,2,3},{4,5,6}}, {{1,2,4},{3,5,6}}, {{1,2,5},{3,4,6}}, {{1,2,6},{3,4,5}}, {{1,3,4},{2,5,6}}, {{1,3,5},{2,4,6}}, {{1,3,6},{2,4,5}}, {{1,4,5},{2,3,6}}, {{1,4,6},{2,3,5}}, {{1,5,6},{2,3,4}}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.7

**Statement:** SIZE-3 CHECK: For each partition, verify h_1, h_2, h_3 do not all preserve it. Example: {{1,2,3},{4,5,6}} under h_1=(1 6 4 3): h_1({1,2,3})={6,2,1}={1,2,6}∉{{1,2,3},{4,5,6}}. All 10 fail. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

