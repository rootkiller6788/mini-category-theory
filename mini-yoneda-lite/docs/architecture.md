# mini-yoneda-lite Architecture

## Package Overview

mini-yoneda-lite is a Lean 4 package implementing the Yoneda lemma and Yoneda embedding.

## Module Hierarchy

```
MiniYonedaLite
├── Core/
│   ├── Basic          (Representable functors, presheaf category, Yoneda embedding)
│   ├── Objects        (Yoneda as a functor)
│   └── Laws           (stub)
├── Morphisms/
│   ├── Hom            (stub)
│   ├── Iso            (stub)
│   └── Equivalence    (stub)
├── Constructions/
│   ├── Products       (stub)
│   ├── Universal      (stub)
│   ├── Subobjects     (stub)
│   └── Quotients      (stub)
├── Properties/
│   ├── Invariants     (stub)
│   ├── Preservation   (stub)
│   └── ClassificationData (stub)
├── Theorems/
│   ├── Basic          (Yoneda lemma statement, Yoneda embedding fully faithful)
│   ├── UniversalProperties (stub)
│   ├── Classification (stub)
│   └── Main           (Yoneda embedding is fully faithful - main theorem)
├── Examples/
│   ├── Standard       (Sample representable functors)
│   └── Counterexamples (stub)
└── Bridges/
    ├── ToAlgebra      (stub)
    ├── ToTopology     (stub)
    ├── ToGeometry     (stub)
    └── ToComputation  (stub)
```

## Key Definitions

- `isRepresentable` — A functor F : C → Set is representable if F ≅ Hom(X, -) for some X
- `presheafCategory` — The category of presheaves [Cᵒᵖ, Set]
- `yonedaEmbedding` — The Yoneda embedding Y : Cᵒᵖ → [C, Set]
- `yonedaLemma` — Nat(Hom(X,-), F) ≅ F(X)
- `yonedaIsFullyFaithful` — The Yoneda embedding is fully faithful
- `representingObjectUnique` — Representing objects are unique up to isomorphism

## Dependencies

- mini-category-core (Category, SetCat, opposite category, product category)
- mini-functor-core (Functor, homFunctor, identityFunctor, constantFunctor)
- mini-natural-transformation (Natural transformation, functor category)
