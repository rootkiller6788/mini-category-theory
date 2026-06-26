# mini-functor-core -- Architecture

## Layer Map

```
┌─────────────────────────────────────────────────────────┐
│                    7. Bridges                           │
│  ToAlgebra  │  ToTopology  │  ToGeometry  │  ToComputation │
├─────────────────────────────────────────────────────────┤
│              6. Examples                                │
│         Standard    │    Counterexamples                │
├─────────────────────────────────────────────────────────┤
│              5. Theorems                                │
│  Basic  │  UniversalProperties  │  Classification  │  Main │
├─────────────────────────────────────────────────────────┤
│              4. Properties                              │
│  Invariants  │  Preservation  │  ClassificationData     │
├─────────────────────────────────────────────────────────┤
│              3. Constructions                           │
│  Subobjects  │  Quotients  │  Products  │  Universal    │
├─────────────────────────────────────────────────────────┤
│              2. Morphisms                               │
│  Hom (Transformations)  │  Iso (Isomorphisms)  │  Equivalence │
├─────────────────────────────────────────────────────────┤
│              1. Core                                    │
│  Basic (FunctorCategory)  │  Objects (Theory)  │  Laws (Naturality) │
└─────────────────────────────────────────────────────────┘
```

## Design Decisions

1. **FunctorCategory as a Category.** The functor category [C, D] is defined as a
   `Category` whose objects are `Functor C D` and morphisms are natural transformations
   (families of D-morphisms indexed by C-objects). This makes [C, D] a first-class category
   that can be used in further constructions.

2. **Hom-functor as core example.** Both covariant C(X, -) and contravariant C(-, X)
   hom-functors are defined. These serve as the foundation for the Yoneda lemma
   and presheaf theory.

3. **Natural transformations as explicit families.** Natural transformations are
   defined both as a `structure` (NaturalTransformation) with component and naturality,
   and with convenience wrappers (NatTrans.id, vcomp, hcomp, whiskerLeft, whiskerRight).

4. **Major theorems as axioms.** The Yoneda lemma, Yoneda embedding, density theorem,
   and Kan extension existence are `axiom` declarations. The package defines
   vocabulary and structure, not full proofs.

5. **Slice/Coslice/Arrow categories.** These diagram categories are defined as
   explicit `Category` instances, enabling reasoning about over/under categories.

## Dependency Hierarchy

```
Core/Basic       (depends on mini-category-core, mini-morphism-system)
Core/Objects     → Core/Basic
Core/Laws        → Core/Basic, Core/Objects

Morphisms/Hom    → Core/Basic, Core/Laws
Morphisms/Iso    → Morphisms/Hom
Morphisms/Equivalence → Morphisms/Iso

Constructions/*  → Morphisms/*
Properties/*     → Constructions/Products, Morphisms/*
Theorems/*       → Properties/*, Constructions/*
Examples/*       → Core/Basic, Theorems/*
Bridges/*        → Morphisms/*, Properties/*, Theorems/*
```
