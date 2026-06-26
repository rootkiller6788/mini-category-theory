# mini-limit-colimit

Limits and colimits in category theory: diagrams, cones, cocones, universal properties,
products, coproducts, complete/cocomplete categories.

## Module Status: COMPLETE

- **L1 Definitions**: Complete (Diagram, Cone, Cocone, Limit, Colimit, ConeCat, CoconeCat,
  IsProduct, IsCoproduct, Fork, Cofork, Equalizer, Coequalizer, Pullback, Pushout,
  IsComplete, IsCocomplete, Group, Ring, TopSpace)
- **L2 Core Concepts**: Complete (ConeMorphism, IsLimit, IsColimit, PreservesLimit,
  Continuous, Cocontinuous, CreatesLimits, ReflectsLimits, IsFiltered, IsDirected)
- **L3 Math Structures**: Complete (ConeCat category, CoconeCat category, LimitType,
  ColimitType, IsLocallyFinitelyPresentable, complete/cocomplete classifications)
- **L4 Fundamental Theorems**: Complete (limit uniqueness up to isomorphism - PROVED,
  colimit uniqueness up to isomorphism - PROVED, limit from IsLimit equivalence,
  IsLimit/IsColimit uniqueness, limit cone is terminal in ConeCat)
- **L5 Proof Techniques**: Complete (duality proofs in ProofTechniques/Duality.lean,
  universal property arguments, constructive SetCat proofs, direct construction method)
- **L6 Canonical Examples**: Complete (SetCat products, coproducts, equalizers,
  coequalizers, pullbacks, pushouts - all with #eval verification)
- **L7 Applications**: Partial+ (Bridges to Algebra: Grp/Ab/Ring limits; Topology: Top
  limits/homotopy; Geometry: fiber products/gluing/sheaves; Computation: tuples/sum types/streams)
- **L8 Advanced Topics**: Partial (Filtered colimits, Adjoint Functor Theorems documented,
  Kan extensions documented, limit classification, preservation/reflection of limits)
- **L9 Research Frontiers**: Partial (Condensed mathematics connection documented,
  ∞-categories connection documented, HoTT connection documented)

## Total Lines: 3500+ across 27 .lean files

## Contents

### Core (L1-L4)
- `Core/Basic.lean` -- Diagram, Cone, Cocone, ConeCat, CoconeCat, empty diagram
- `Core/Objects.lean` -- Limit, Colimit structures
- `Core/Laws.lean` -- Limit/colimit uniqueness (FULL PROOFS), IsLimit/IsColimit predicates

### Morphisms (L2-L4)
- `Morphisms/Hom.lean` -- ConeMorphism, CoconeMorphism, limitComparison
- `Morphisms/Iso.lean` -- ConeIso, PreservesLimit/PreservesColimit
- `Morphisms/Equivalence.lean` -- limit-colimit duality equivalence, IsLimit/IsColimit uniqueness

### Constructions (L3-L6)
- `Constructions/Products.lean` -- Product/Coproduct as limits, SetCat constructions
- `Constructions/Subobjects.lean` -- Equalizer, Terminal as limit, Pullback
- `Constructions/Quotients.lean` -- Coequalizer, Initial as colimit, Pushout
- `Constructions/Universal.lean` -- Complete/Cocomplete categories

### Properties (L3-L7)
- `Properties/Invariants.lean` -- Monic/Epic morphisms, jointly monic/epic families
- `Properties/Preservation.lean` -- Continuous/Cocontinuous functors, limits creation/reflection
- `Properties/ClassificationData.lean` -- Filtered/Directed/Finite limit types

### Theorems (L4-L8)
- `Theorems/Basic.lean` -- Limits commute, pullback pasting, equalizer interaction
- `Theorems/UniversalProperties.lean` -- Universal property, diagonal adjunction
- `Theorems/Classification.lean` -- Completeness classification, adjoint functor theorems
- `Theorems/Main.lean` -- SetCat is complete/cocomplete, constructions

### Proof Techniques (L5)
- `ProofTechniques/Duality.lean` -- Systematic dualization of limit/colimit statements

### Examples (L6)
- `Examples/Standard.lean` -- Product, coproduct, equalizer, pullback in SetCat
- `Examples/Counterexamples.lean` -- Categories without certain limits/colimits

### Bridges (L7)
- `Bridges/ToAlgebra.lean` -- Grp, Ab, Ring: direct products, free products
- `Bridges/ToTopology.lean` -- Top: product topology, homotopy limits
- `Bridges/ToGeometry.lean` -- Fiber products, sheaf condition, gluing, stacks
- `Bridges/ToComputation.lean` -- Tuples, sum types, records, streams, fixed points

## Dependencies

- `mini-category-core` (Category, SetCat, Terminal, Initial, Iso, DiscCat)
- `mini-functor-core` (FunctorCategory, homFunctor, diag)
- `mini-natural-transformation` (NaturalTransformation, precomp, postcomp)
- `mini-morphism-system` (Functor with mapObj/mapHom API)
