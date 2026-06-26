# mini-functor-core

Functor theory core: functor categories, diagrams, hom-functors, presheaf basics.

## Contents

- `Core/Basic.lean` — FunctorCategory [C,D], homFunctor, homFunctorOp, diag, eval, SliceCat
- `Core/Objects.lean` — Object instance registration with kernel
- `Core/Laws.lean` — Functor composition laws (identity, associativity), naturality laws
- `Morphisms/Hom.lean` — Functor homomorphisms (transformations between functor objects)
- `Morphisms/Iso.lean` — Functor isomorphisms in [C,D]
- `Morphisms/Equivalence.lean` — stub
- `Constructions/Products.lean` — Functor category [C,D] as exponential, eval functor
- `Constructions/Universal.lean` — stub
- `Constructions/Subobjects.lean` — stub
- `Constructions/Quotients.lean` — stub
- `Properties/Invariants.lean` — stub
- `Properties/Preservation.lean` — stub
- `Properties/ClassificationData.lean` — stub
- `Theorems/Basic.lean` — stub
- `Theorems/UniversalProperties.lean` — stub
- `Theorems/Classification.lean` — stub
- `Theorems/Main.lean` — stub
- `Examples/Standard.lean` — SetCat functors, forgetful functors
- `Examples/Counterexamples.lean` — stub
- `Bridges/ToAlgebra.lean` — stub
- `Bridges/ToTopology.lean` — stub
- `Bridges/ToGeometry.lean` — stub
- `Bridges/ToComputation.lean` — stub

## Dependencies

- `mini-category-core` (for Category, SetCat, opposite, product)
- `mini-morphism-system` (for Functor, NaturalTransformation)
