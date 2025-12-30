# Regional Associativity: A Coq Formalization

## Overview

This repository formalizes the mathematical framework of "Associativity Under Gluing" 
from a Whiteheadian process-relational perspective. The central insight is that when 
algebraic data on overlapping regions are glued together, associativity can fail in 
a controlled way: the failure localizes to triple overlaps and forms a Čech cohomology 
class that either vanishes (allowing canonical completion) or persists as irreducible 
tripartite structure.

## Philosophical Motivation

In Whitehead's Process and Reality, the fundamental units of existence are not 
point-particles but "actual occasions" — achieved unities of experience with genuine 
extension. This formalization treats regions as primitive (not sets of points) and 
gluing as a process of synthesis (not set-theoretic union).

Key correspondences:

| Mathematical Concept | Whiteheadian Interpretation |
|---------------------|----------------------------|
| Region R | Actual occasion in its spatial aspect |
| Lattice join R ∪ S | Potential for synthesis |
| Lattice meet R ∩ S | Mutual relevance / prehension |
| Algebra A(R) | Eternal objects ingressible in R |
| Structure map ι : A(R) → A(S) | Extension of predicates |
| Correction term β | Novelty emerging from synthesis |
| Associator α | Contrast / incompatibility |
| Edge completion A^e | Satisfaction / final unity |

## File Structure

```
coq/
├── RegionLattice.v          # Finite distributive lattices of regions
├── AlgebraicAssignment.v    # Precosheaves of algebras with injective maps
├── BinaryGluing.v           # Gluing data: the β-correction terms
├── Associator.v             # Localization lemma (Lemma 4.2)
├── CechCocycle.v            # Cocycle theorem (Theorem 5.6)
├── EdgeCompletion.v         # Universal completion (Section 6-7)
├── Examples/
│   ├── DualNumbers.v        # Z[ε]/(ε²) toy model
│   └── S3NonVanishing.v     # Five regions on S³ with [α] ≠ 0
└── README.md                # This file
```

## Mathematical Content

### 1. Region Lattices (RegionLattice.v)

A **region lattice** is a bounded distributive lattice (Reg, ∅, ⊤, ∪, ∩) where:
- Regions are primitive, not sets of points
- Join (∪) represents potential synthesis
- Meet (∩) represents mutual relevance
- Distributivity encodes the inclusion-exclusion principle

Key definitions:
- `RegionLattice` — the type class for region lattices
- `triple_meet` — the triple overlap U ∩ V ∩ W
- `incl` — the inclusion partial order R ⊆ S := (R ∩ S = R)

Key lemmas:
- `triple_overlap_join` — distributivity for overlaps: (U ∪ V) ∩ W = (U ∩ W) ∪ (V ∩ W)

### 2. Algebraic Assignments (AlgebraicAssignment.v)

An **algebraic assignment** is a functor A : Reg → Alg_k with:
- For each region R, a k-algebra A(R)
- For each inclusion R ⊆ S, a structure map ι : A(R) → A(S)
- Composition: ι_{R,T} = ι_{S,T} ∘ ι_{R,S}

The crucial **injectivity convention**: all structure maps are injective. This allows:
- Restriction of elements to sub-regions (when supported)
- Identification of A(R) with a subalgebra of A(S)

Key definitions:
- `AlgebraicAssignment` — the type class
- `InjectiveAssignment` — the injectivity assumption
- `supported_on` — predicate for support of elements
- `restrict` — the restriction operation (partial)

### 3. Binary Gluing (BinaryGluing.v)

A **binary gluing datum** for regions U, V consists of:
- A bilinear gluing map m : A(U) ⊗ A(V) → A(U ∪ V)
- A bilinear correction map β : A(U) ⊗ A(V) → A(U ∩ V)

The decomposition formula (Equation 1):

```
m_{U,V}(a,b) = ι(a ·_U b|_U) + ι(a|_V ·_V b) - ι(a|_Γ ·_Γ b|_Γ) + ι(β(a,b))
```

This is inclusion-exclusion plus novelty: U-contribution + V-contribution - double-counting + emergent.

Key definitions:
- `BinaryGluingDatum` — the gluing data record
- `BinaryGluingSystem` — compatible data for all pairs
- `RestrictionCompatible` — coherence under restriction

### 4. The Associator (Associator.v)

The **associator** measures failure of associativity:

```
α_{U,V,W}(a,b,c) := (a · b) · c - a · (b · c)
```

**Lemma 4.2 (Localization)**: The associator is supported on the triple overlap:

```
α_{U,V,W}(a,b,c) ∈ A(U ∩ V ∩ W)
```

The proof classifies terms by support type and shows:
- Type I (interior): cancel by local associativity
- Type II (binary overlap): cancel by overlap associativity  
- Type III/IV (mixed/correction): land on Λ by intersection considerations

Key definitions:
- `assoc` — the associator in A(U ∪ V ∪ W)
- `assoc_lifted` — the lifted associator in A(U ∩ V ∩ W)
- `associator_trilinear` — trilinearity record

### 5. The Čech Cocycle (CechCocycle.v)

**Theorem 5.6 (Cocycle)**: The lifted associator is a Čech 3-cocycle:

```
(δα)_{ijkl} = α_{jkl}|_Q - α_{ikl}|_Q + α_{ijl}|_Q - α_{ijk}|_Q = 0
```

where Q = U_i ∩ U_j ∩ U_k ∩ U_l.

The proof uses the Mac Lane pentagon identity: the five parenthesizations of (a·b·c·d) 
form a closed pentagon, and traversing the boundary gives the cocycle condition.

**Theorem 5.8 (Gauge Invariance)**: The cohomology class [α] is independent of:
- Choice of test elements (trilinearity)
- Choice of β-correction gauge

Key definitions:
- `Cech0`, `Cech1`, `Cech2`, `Cech3` — Čech cochain groups
- `coboundary_2_3` — the coboundary operator δ
- `assoc_cochain` — the associator as a 2-cochain
- `cohomologous` — equivalence relation on cocycles

### 6. Edge Completion (EdgeCompletion.v)

When [α] = 0, there exists a **trivializing cochain** Θ with α = δΘ.

**Definition 6.1**: The edge-completed algebra is:

```
A^e(R) := A(R) ⊕ ⨁_{J : |J| ≥ 2, U_J ⊆ R} A(U_J)
```

Elements are pairs (x, ξ) with interior and edge components.

**Definition 6.3**: Edge-corrected multiplication:

```
(x, ξ) ·^e (y, η) := (m(x,y), ξ + η + Θ(x,y))
```

**Theorem 6.4**: Edge-corrected multiplication is strictly associative.

**Theorem 7.2 (Universal Property)**: A^e is initial among strictly associative 
recipients of A. Any boundary-compatible morphism Φ : A → B to a strict B 
factors uniquely through A^e.

Key definitions:
- `EdgeAlgebra` — the edge-completed algebra record
- `edge_mult` — edge-corrected multiplication
- `BoundaryCompatibleMorphism` — morphisms respecting gluing
- `StrictCosheaf` — strictly associative recipients

### 7. Examples

**DualNumbers.v**: The toy model Z[ε]/(ε²) where:
- Every region gets the same algebra
- Corrections β_{ij}(a,b) = λ_{ij} · π₀(a) · π₀(b) · ε
- Obstruction Δ = λ_{UV} + λ_{S,W} - λ_{VW} - λ_{U,T}
- Vanishing iff Δ = 0

**S3NonVanishing.v**: Five regions covering S³ where:
- Nerve ≅ ∂Δ⁴ ≅ S³
- Ȟ³(nerve; Z) ≅ Z
- Cyclic λ-assignment creates non-trivial holonomy
- [α] generates Ȟ³, cannot be gauged away

## Building

```bash
cd coq
coq_makefile -f _CoqProject -o Makefile
make
```

## Proof Status

| File | Theorems | Status |
|------|----------|--------|
| RegionLattice.v | Lattice laws | ✓ Complete |
| AlgebraicAssignment.v | Structure map composition | ✓ Complete |
| BinaryGluing.v | Decomposition coherence | ◐ Partial |
| Associator.v | Localization lemma | ◐ Admitted |
| CechCocycle.v | Cocycle theorem | ◐ Admitted |
| EdgeCompletion.v | Associativity, universal property | ◐ Admitted |
| Examples/DualNumbers.v | Δ calculation | ✓ Complete |
| Examples/S3NonVanishing.v | Non-vanishing | ◐ Partial |

## Dependencies

- Coq 8.16+
- No external libraries (self-contained)

## Extensions

Planned extensions include:
- **Agda formalization** with HoTT/cubical connections
- **Lean port** for mathlib compatibility
- **Computational extraction** to OCaml
- **Applications**: 
  - Yang-Mills mass gap
  - Quantum information / strong subadditivity
  - AI safety verification architectures

## References

- Moore, D. "Associativity Under Gluing: Čech Obstructions and Canonical Edge Completion"
- Whitehead, A.N. *Process and Reality* (1929)
- Mac Lane, S. "Natural Associativity and Commutativity" (1963)
- Costello, K. & Gwilliam, O. *Factorization Algebras in Quantum Field Theory* (2017)

## License

MIT License

## Contact

Duston Moore — dhwcmoore@gmail.com
