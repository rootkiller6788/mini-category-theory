# Mini Natural Transformation

An independent Lean 4 Lake package providing natural transformations between functors.

## Overview

Natural transformations are structure-preserving maps between functors. This package defines:

- `NaturalTransformation F G` — a natural transformation from functor F to G
- Vertical composition of natural transformations
- Horizontal composition (whiskering)
- Natural isomorphisms

## Dependencies

- `mini-category-core`
- `mini-functor-core`
- `mini-morphism-system`

## Modules

- **Core**: Basic definitions, identity, naturality law, interchange law
- **Morphisms**: Horizontal composition, natural isomorphisms, equivalences
- **Constructions**: Products, universal constructions, subobjects, quotients
- **Properties**: Invariants, preservation, classification data
- **Theorems**: Main theorems with proofs
- **Examples**: Standard examples and counterexamples
- **Bridges**: Connections to algebra, topology, geometry, computation

## Build

```
lake build
```
