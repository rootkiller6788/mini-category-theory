# Course Tree — mini-morphism-system

## Prerequisites
```
mini-object-kernel (0. mini-math-kernel)
  └── mini-category-core (category theory basics)
        └── mini-morphism-system (THIS MODULE)
              ├── mini-adjunction-system (future)
              ├── mini-limit-colimit (future)
              └── mini-monad-system (future)
```

## Internal Dependency Graph
```
Core/Basic.lean (Functor, Functor.const)
  ├── Core/Objects.lean (Functor.id, Functor.comp, Iso, MorphismClass, HasLLP, Orthogonal, FactorizationSystem, LiftingSystem)
  │     ├── Core/Laws.lean (Functor laws, Iso properties, factorization laws)
  │     │     ├── Morphisms/Hom.lean (Full, Faithful, Cat)
  │     │     │     ├── Morphisms/Iso.lean (FunctorIso, Equivalence)
  │     │     │     │     └── Morphisms/Equivalence.lean (Equivalence properties)
  │     │     │     └── Properties/Preservation.lean
  │     │     ├── Properties/ClassificationData.lean (Epi, Mono, ModelStructureData)
  │     │     ├── Properties/Invariants.lean (Stability, SaturatedClass)
  │     │     ├── Constructions/Products.lean (Product FS)
  │     │     ├── Constructions/Universal.lean (Saturation, Free FS)
  │     │     ├── Constructions/Subobjects.lean (Restricted FS)
  │     │     └── Constructions/Quotients.lean (Quotient FS, Projection)
  │     ├── Theorems/Basic.lean (EpiMono factorization, SetCat)
  │     │     ├── Theorems/UniversalProperties.lean (Universal factorization)
  │     │     ├── Theorems/Classification.lean (Orthogonal FS, WFS, ModelCategory)
  │     │     └── Theorems/Main.lean (SetCat FS, main construction)
  │     ├── Examples/Standard.lean (8 examples)
  │     ├── Examples/Counterexamples.lean (6 counterexamples)
  │     ├── Bridges/ToAlgebra.lean
  │     ├── Bridges/ToTopology.lean
  │     ├── Bridges/ToGeometry.lean
  │     └── Bridges/ToComputation.lean
  └── (imported by MiniMorphismSystem.lean which aggregates all)
```

## Knowledge Dependencies
- **L1 Definitions needed before L2**: Functor, Iso before functor laws
- **L2 Concepts needed before L4 Theorems**: Iso properties before equivalence theorem
- **L3 Structures needed before L4 Theorems**: FactorizationSystem before factorization uniqueness
- **L5 Proof techniques used throughout**: Calc blocks, naturality, diagonal arguments

## Learning Path
1. Start with Core/Basic.lean → understand Functor definition
2. Core/Objects.lean → understand Iso, FactorizationSystem
3. Core/Laws.lean → basic theorems about functors and isos
4. Morphisms/Hom.lean → functor properties (full, faithful)
5. Morphisms/Iso.lean → FunctorIso, Equivalence definition
6. Morphisms/Equivalence.lean → equivalence properties
7. Theorems/Basic.lean → (epi, mono) factorization in SetCat
8. Theorems/Classification.lean → advanced factorization systems
9. Examples → concrete examples and counterexamples
10. Bridges → applications to algebra, topology, geometry, computation
