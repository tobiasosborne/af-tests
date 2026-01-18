# Proof Export

## Node 1

**Statement:** The partition B_0 = {{1,4}, {2,5}, {3,6}} is preserved setwise by each h_i, where h_1 = (1 6 4 3), h_2 = (1 2 4 5), h_3 = (5 6 2 3). Specifically: (1) h_1({1,4}) = {3,6}, h_1({2,5}) = {2,5}, h_1({3,6}) = {1,4}; (2) h_2({1,4}) = {2,5}, h_2({2,5}) = {1,4}, h_2({3,6}) = {3,6}; (3) h_3({1,4}) = {1,4}, h_3({2,5}) = {3,6}, h_3({3,6}) = {2,5}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** We prove that each h_i permutes the blocks of B_0 = {{1,4}, {2,5}, {3,6}} by direct computation. The proof splits into three parts: (1) showing h_1 permutes B_0, (2) showing h_2 permutes B_0, and (3) showing h_3 permutes B_0. Each part requires computing the image of each block under the respective cycle.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** Part 1: h_1 = (1 6 4 3) permutes B_0. We compute the image of each block:
- For {1,4}: h_1(1) = 6 and h_1(4) = 3, so h_1({1,4}) = {6,3} = {3,6}.
- For {2,5}: h_1(2) = 2 and h_1(5) = 5 (since 2,5 are not in the cycle), so h_1({2,5}) = {2,5}.
- For {3,6}: h_1(3) = 1 and h_1(6) = 4, so h_1({3,6}) = {1,4}.
Thus h_1 maps B_0 to itself: {1,4} -> {3,6}, {2,5} -> {2,5}, {3,6} -> {1,4}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.3

**Statement:** Part 2: h_2 = (1 2 4 5) permutes B_0. We compute the image of each block:
- For {1,4}: h_2(1) = 2 and h_2(4) = 5, so h_2({1,4}) = {2,5}.
- For {2,5}: h_2(2) = 4 and h_2(5) = 1, so h_2({2,5}) = {4,1} = {1,4}.
- For {3,6}: h_2(3) = 3 and h_2(6) = 6 (since 3,6 are not in the cycle), so h_2({3,6}) = {3,6}.
Thus h_2 maps B_0 to itself: {1,4} -> {2,5}, {2,5} -> {1,4}, {3,6} -> {3,6}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.4

**Statement:** Part 3: h_3 = (5 6 2 3) permutes B_0. We compute the image of each block:
- For {1,4}: h_3(1) = 1 and h_3(4) = 4 (since 1,4 are not in the cycle), so h_3({1,4}) = {1,4}.
- For {2,5}: h_3(2) = 3 and h_3(5) = 6, so h_3({2,5}) = {3,6}.
- For {3,6}: h_3(3) = 5 and h_3(6) = 2, so h_3({3,6}) = {5,2} = {2,5}.
Thus h_3 maps B_0 to itself: {1,4} -> {1,4}, {2,5} -> {3,6}, {3,6} -> {2,5}.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.5

**Statement:** Conclusion: From Parts 1-3, each h_i maps B_0 bijectively to itself. Specifically:
- h_1: ({1,4}, {2,5}, {3,6}) -> ({3,6}, {2,5}, {1,4})
- h_2: ({1,4}, {2,5}, {3,6}) -> ({2,5}, {1,4}, {3,6})
- h_3: ({1,4}, {2,5}, {3,6}) -> ({1,4}, {3,6}, {2,5})
Since each image is a permutation of the three blocks, B_0 is preserved setwise by each h_i. QED.

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

