# Course Tree — mini-category-core

## Prerequisites

This module depends on:

```
mini-object-kernel (0. mini-math-kernel)
├── TheoryName: hierarchical theory naming
├── Object typeclass: theory/objName/repr
├── Subobject: carrier + embedding + injective
└── Quotient: rel + equiv + proj
```

## Internal Dependency Tree

```
Core/Basic.lean
├── Core/Objects.lean
│   └── Core/Laws.lean
│       └── Morphisms/Hom.lean
│           ├── Morphisms/Iso.lean
│           │   └── Morphisms/Equivalence.lean
│           │       └── Theorems/Main.lean
│           ├── Constructions/Universal.lean
│           │   ├── Theorems/Basic.lean
│           │   │   └── Theorems/UniversalProperties.lean
│           │   └── Properties/Preservation.lean
│           └── Constructions/Products.lean
│               └── Bridges/ToComputation.lean
├── Constructions/Subobjects.lean
├── Constructions/Quotients.lean
├── Properties/Invariants.lean
│   └── Properties/ClassificationData.lean
│       ├── Theorems/Classification.lean
│       ├── Examples/Standard.lean
│       ├── Examples/Counterexamples.lean
│       └── Bridges/ToAlgebra.lean
├── Bridges/ToTopology.lean
└── Bridges/ToGeometry.lean
```

## Key Dependency Chains

1. **Category → Iso → Functor → Equivalence → Yoneda**
   `Basic → Objects → Laws → Hom → Iso → Equivalence → Main`

2. **Category → Universal → Products → CCC**
   `Basic → Universal → Products → ToComputation`

3. **Category → Mono/Epi → Split Mono/Epi → Iso ←→ Split Mono+Epi**
   `Basic → Objects → Hom → Iso`

4. **Category → Subobject → Subobject Classifier**
   `Basic → Hom → Subobjects`

5. **Category → Congruence → Quotient Category**
   `Basic → Quotients`

6. **Category → Invariants → Classification → Examples**
   `Basic → Invariants → ClassificationData → Classification → Standard/Counterexamples`

## Cross-Module References

| Source | Target | Dependency |
|--------|--------|------------|
| mini-category-core | mini-object-kernel | `require` in lakefile.lean |
| Bridges/ToAlgebra | Properties/ClassificationData | `import` MonoidCat, GroupCat |
| Bridges/ToComputation | Constructions/Products | `import` HasBinaryProducts |
| Theorems/Main | Morphisms/Equivalence | `import` equivalence_iff_ff_es |
| Theorems/Basic | Constructions/Universal + Products | `import` Terminal, Product |
