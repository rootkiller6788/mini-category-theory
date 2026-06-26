# Architecture

## Package: mini-monad-core

Monad theory: Monad (T, η, μ), Kleisli category, Eilenberg-Moore category, monad laws.

### Module Organization

- **Core/** — Fundamental definitions: Monad structure, Kleisli category, monad laws
- **Morphisms/** — Monad morphisms, isomorphisms, equivalences
- **Constructions/** — Constructions: Eilenberg-Moore category, products, subobjects, quotients
- **Properties/** — Properties and invariants of monads
- **Theorems/** — Theorems: adjunction → monad, universal properties, classification
- **Examples/** — Standard examples and counterexamples
- **Bridges/** — Connections to algebra, topology, geometry, computation

### Dependency Graph

```
mini-category-core + mini-functor-core + mini-natural-transformation + mini-adjunction
    ↓
mini-monad-core (Monad, KleisliCat, EMCat, fromAdjunction)
```
