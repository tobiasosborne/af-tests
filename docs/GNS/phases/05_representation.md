# Phase 5: GNS Representation

## Overview

Define π_φ(a) : H_φ → H_φ where π_φ(a)[b] = [ab].

## Files

| File | LOC Target | Actual LOC | Status | Key Content |
|------|------------|------------|--------|-------------|
| `Representation/PreRep.lean` | 60-80 | 96 | **Proven** | π(a)[b] = [ab] on quotient |
| `Representation/Bounded.lean` | 60-80 | 115 | **Proven** | ‖π(a)‖ ≤ ‖a‖ |
| `Representation/Extension.lean` | 60-80 | 160 | **Proven** | Extend to completion |
| `Representation/Star.lean` | 70-90 | 111 | **Proven** | π(a*) = π(a)* |

## Definitions

```lean
def gnsPreRep (φ : State A) (a : A) : gnsQuotient φ →ₗ[ℂ] gnsQuotient φ :=
  gnsLeftAction φ a

noncomputable def gnsPreRepCLM (φ : State A) (a : A) :
    gnsQuotient φ →L[ℂ] gnsQuotient φ :=
  (gnsPreRep φ a).mkContinuous ‖a‖ (gnsPreRep_norm_le φ a)

noncomputable def gnsRep (φ : State A) (a : A) :
    gnsHilbertSpace φ →L[ℂ] gnsHilbertSpace φ :=
  (gnsPreRepCLM φ a).extend (gnsEmbed φ) (gnsEmbed φ) ...
```

## Key Lemmas

### PreRep.lean
- `gnsPreRep_mk` - π(a)[b] = [ab]
- `gnsPreRep_mul` - π(ab) = π(a) ∘ π(b)
- `gnsPreRep_one` - π(1) = id
- `gnsPreRep_add` - π(a+b) = π(a) + π(b)

### Bounded.lean
- `gnsPreRep_norm_le` - ‖π(a)x‖ ≤ ‖a‖·‖x‖
- Key: Use C*-identity `a*a ≤ ‖a‖²·1` and positivity of φ

### Extension.lean
- `gnsRep_embed` - π(a)(embed x) = embed(πpre(a)x)
- `gnsRep_cyclicVector` - π(a)Ω = embed[a]
- `gnsRep_mul`, `gnsRep_one`, `gnsRep_add`

### Star.lean
- `gnsRep_star` - π(a*) = π(a).adjoint
- `gnsStarAlgHom` - The *-algebra homomorphism

## Boundedness Proof

```
‖[ab]‖² = φ((ab)*(ab)) = φ(b*a*ab)
Key: a*a ≤ ‖a‖²·1 in C*-algebra order
So: φ(b*a*ab) ≤ ‖a‖²·φ(b*b) = ‖a‖²·‖[b]‖²
```

## Dependencies

```
HilbertSpace/Completion.lean
            │
      ┌─────┴─────┐
      ▼           ▼
  PreRep.lean  Bounded.lean
      │           │
      └─────┬─────┘
            ▼
     Extension.lean
            │
            ▼
       Star.lean
```
