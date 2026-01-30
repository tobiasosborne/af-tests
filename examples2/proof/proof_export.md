# Proof Export

## Node 1

**Statement:** For self-adjoint A in a free *-algebra with Archimedean quadratic module M: A is in the closure of M if and only if phi(A) >= 0 for all M-positive states phi

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.1

**Statement:** If A is in the closure of M, then phi(A) >= 0 for all M-positive states phi

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.1.1

**Statement:** A is in the closure of M, so there exists a sequence (m_n) in M with ||A - m_n||_M converging to 0

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.1.2

**Statement:** For any M-positive state phi: |phi(A) - phi(m_n)| <= ||A - m_n||_M

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.1.3

**Statement:** Since phi(m_n) >= 0 for all n and phi(A) = lim phi(m_n), we have phi(A) >= 0

**Type:** qed

**Inference:** assumption

**Status:** validated

**Taint:** clean

### Node 1.2

**Statement:** If phi(A) >= 0 for all M-positive states phi, then A is in the closure of M

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.1

**Statement:** M intersect the self-adjoint elements is a generating cone for the self-adjoint part of A_0

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.1.1

**Statement:** For any self-adjoint x: x = (1/4)(1+x)*(1+x) - (1/4)(1-x)*(1-x)

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.1.2

**Statement:** Both (1+x)*(1+x) and (1-x)*(1-x) are of the form a*a, hence lie in M

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.1.3

**Statement:** Every self-adjoint element is a difference of two elements in M intersect the self-adjoints

**Type:** qed

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.2

**Statement:** Assume phi(A) >= 0 for all M-positive states phi, but A is not in the closure of M

**Type:** local_assume

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.3

**Statement:** Since the closure of M is closed and A is not in it, epsilon := inf{||A - m||_M : m in closure(M)} > 0

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.4

**Statement:** M intersect span{A} equals {0}

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.4.1

**Statement:** Case lambda > 0 and lambda A in M: Then A = (1/lambda)(lambda A) is in M, hence in closure(M), contradicting A not in closure(M)

**Type:** case

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.4.2

**Statement:** Case lambda < 0 and lambda A in M: Then -A = (1/|lambda|)(lambda A) is in M

**Type:** case

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.4.3

**Statement:** If -A is in M then phi(-A) >= 0 for all phi, so phi(A) <= 0. Combined with hypothesis phi(A) >= 0, we get phi(A) = 0 for all phi

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.4.4

**Statement:** phi(A) = 0 for all phi implies ||A||_M = 0, hence A is in closure(M), contradiction

**Type:** qed

**Inference:** assumption

**Status:** validated

**Taint:** clean

###### Node 1.2.4.4.1

**Statement:** By definition, ||A||_M = sup{|phi(A)| : phi in S_M}. Since phi(A) = 0 for all phi, we have ||A||_M = 0

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

###### Node 1.2.4.4.2

**Statement:** 0 is in M (since M contains a*a for any a, including 0 = 0*0), hence 0 is in closure(M)

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

###### Node 1.2.4.4.3

**Statement:** ||A - 0||_M = ||A||_M = 0, so the distance from A to closure(M) is 0, hence A is in closure(M)

**Type:** qed

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.5

**Statement:** By Riesz-Kantorovich, extend the functional psi_0(lambda A) = -lambda epsilon to all self-adjoints with psi >= 0 on M

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

#### Node 1.2.6

**Statement:** Normalizing psi gives an M-positive state phi_1 with phi_1(A) < 0, contradicting the hypothesis

**Type:** local_discharge

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.6.1

**Statement:** Define phi on A_0 by phi(a) = psi(Re(a)) + i psi(Im(a))

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.6.2

**Statement:** psi(1) > 0: Since 1 = 1*1 is in M, psi(1) >= 0. If psi(1) = 0, then by Archimedean property psi(a*a) = 0 for all a, hence psi = 0 on self-adjoints, contradicting psi(A) = -epsilon

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.6.3

**Statement:** Set phi_1 = phi / psi(1). Then phi_1(1) = 1 and phi_1(m) >= 0 for m in M, so phi_1 is M-positive

**Type:** claim

**Inference:** assumption

**Status:** validated

**Taint:** clean

##### Node 1.2.6.4

**Statement:** But phi_1(A) = psi(A)/psi(1) = -epsilon/psi(1) < 0, contradicting the hypothesis that phi(A) >= 0 for all M-positive phi

**Type:** qed

**Inference:** assumption

**Status:** validated

**Taint:** clean

