# Archimedean Closure Learnings

This directory contains technical discoveries from the Archimedean Closure formalization.

## Index

| File | Topic | Key Content |
|------|-------|-------------|
| [LEARNINGS_star.md](LEARNINGS_star.md) | Star Structure | FreeAlgebra star issues, ℝ vs ℂ decision |
| [LEARNINGS_proofs.md](LEARNINGS_proofs.md) | Proof Patterns | Non-commutative tactics, Commute lemmas |
| [LEARNINGS_states.md](LEARNINGS_states.md) | States & Bounds | MPositiveState, Cauchy-Schwarz, Archimedean bounds |
| [LEARNINGS_misc.md](LEARNINGS_misc.md) | Miscellaneous | Section scoping, FunLike, QuadraticModule |
| [LEARNINGS_topology.md](LEARNINGS_topology.md) | Topology | Closedness, Tychonoff, seminorm closure |
| [LEARNINGS_dual.md](LEARNINGS_dual.md) | Dual Characterization | Riesz extension, span intersection, Hahn-Banach |
| [LEARNINGS_extension.md](LEARNINGS_extension.md) | Extension Theorems | Why standard theorems don't apply, ProperCone path |

## Quick Reference: Key Patterns

### Non-Commutative Expansion
```lean
simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
abel
```

### Additive Simplification
```lean
have h : expr = (n : ℕ) • z := by abel
rw [h, nsmul_eq_mul, Nat.cast_ofNat]
```

### Scalar Cancellation
```lean
have h : (b : R) * x = (b : ℝ) • x := by rw [Algebra.smul_def]; rfl
rw [h, smul_smul]
norm_num
```

### Commutativity in Non-Commutative Rings
```lean
have hcomm : Commute a b := by
  apply Commute.add_left
  · exact (Commute.one_left _).sub_right ...
  · exact (Commute.one_right _).sub_right (Commute.refl _)
rw [hcomm.mul_self_sub_mul_self_eq]
```

### Complexified Positivity Pattern
For a self-adjoint operator T on real Hilbert space H_ℝ with ⟨x, Tx⟩_ℝ ≥ 0:
```lean
-- On complexification H_ℂ = H_ℝ ⊕ iH_ℝ:
-- Re⟨p, T_ℂ p⟩_ℂ = ⟨p.1, T p.1⟩_ℝ + ⟨p.2, T p.2⟩_ℝ ≥ 0
-- Uses: Complexification.inner_re, add_nonneg
```
Key: `Complexification.inner_re` gives `Re⟨p,q⟩_ℂ = ⟨p.1,q.1⟩_ℝ + ⟨p.2,q.2⟩_ℝ`.

## Critical Decision: FreeStarAlgebra Uses ℝ

The algebra is `FreeAlgebra ℝ (Fin n)`, NOT `FreeAlgebra ℂ`.

**Why**: Over ℂ, scalar extraction fails because `star (algebraMap I) * algebraMap I = -1`,
which has negative real part. Over ℝ, `c² ≥ 0` always.

See [LEARNINGS_star.md](LEARNINGS_star.md) for full details.
