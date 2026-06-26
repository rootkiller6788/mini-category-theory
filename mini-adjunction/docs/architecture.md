# Architecture

## Package: mini-adjunction

Adjunctions: the central concept in category theory. An adjunction F ⊣ G between functors F : C → D and G : D → C.

### Module Organization

- **Core/** — Fundamental definitions: Adjunction structure via unit/counit, hom-set adjunction, triangle identities
- **Morphisms/** — Morphism concepts for adjunctions: Hom, Iso, Equivalence
- **Constructions/** — Categorical constructions via adjunctions: Products, Universal, Subobjects, Quotients
- **Properties/** — Properties of adjunctions: Invariants, Preservation (LAPC, RAPL), ClassificationData
- **Theorems/** — Theorems about adjunctions: Basic, UniversalProperties, Classification, Main
- **Examples/** — Standard examples (Free/forgetful) and counterexamples
- **Bridges/** — Connections to algebra, topology, geometry, computation

### Dependency Graph

```
mini-object-kernel
    ↓
mini-category-core (Category, SetCat)
    ↓
mini-morphism-system (Functor)
    ↓
mini-functor-core (FunctorCategory, hom-functors)
    ↓
mini-natural-transformation (NaturalTransformation, ⇒)
    ↓
mini-adjunction (Adjunction F ⊣ G, unit/counit, hom-adjunction, triangle identities)
    ↓
future packages (limits, monads, Kan extensions, ...)
```
