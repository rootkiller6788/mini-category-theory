# mini-limit-colimit -- Architecture

## Layer Map

```
┌─────────────────────────────────────────────────────────────────┐
│                    7. Bridges                                   │
│  ToAlgebra  │  ToTopology  │  ToGeometry  │  ToComputation     │
├─────────────────────────────────────────────────────────────────┤
│              6. Examples                                        │
│         Standard    │    Counterexamples                        │
├─────────────────────────────────────────────────────────────────┤
│              5. Theorems                                        │
│  Basic  │  UniversalProperties  │  Classification  │  Main     │
├─────────────────────────────────────────────────────────────────┤
│              4. Properties                                      │
│  Invariants  │  Preservation  │  ClassificationData             │
├─────────────────────────────────────────────────────────────────┤
│              3. Constructions                                   │
│  Products  │  Universal  │  Subobjects  │  Quotients             │
├─────────────────────────────────────────────────────────────────┤
│              2. Morphisms                                       │
│  Hom (ConeMorphism)  │  Iso (stub)  │  Equivalence (stub)      │
├─────────────────────────────────────────────────────────────────┤
│              1. Core                                            │
│  Basic (Diagram, Cone, Cocone)  │  Objects (Limit, Colimit)     │
│  Laws (uniqueness laws)                                        │
└─────────────────────────────────────────────────────────────────┘
```

## Design Decisions

1. **Diagram as Functor.** A `Diagram J C` is a functor `J → C`. This is the standard
   definition and allows all functor theory to apply immediately.

2. **Limit as terminal cone.** `Limit D` is a cone with a unique mediating morphism
   from any other cone. This is the clean universal-property definition.

3. **Colimit as initial cocone.** `Colimit D` is a cocone with a unique mediating
   morphism to any other cocone.

4. **Products as limits over discrete diagrams.** `IsProduct` defines the familiar
   binary product via explicit `fst`, `snd`, `mediate`, without requiring the
   full Diagram definition.

5. **Dual definitions throughout.** Every limit concept has a dual colimit concept.

## Dependency Hierarchy

```
Core/Basic       (depends on: mini-category-core, mini-morphism-system)
Core/Objects     → Core/Basic
Core/Laws        → Core/Basic, Core/Objects

Morphisms/Hom    → Core/Basic, mini-functor-core, mini-natural-transformation
Morphisms/Iso    → Core/Basic (stub)
Morphisms/Equivalence → Core/Basic (stub)

Constructions/Products    → Core/Basic, Core/Objects
Constructions/Universal   → Core/Basic, Core/Objects, mini-category-core
Constructions/Subobjects  → Core/Basic (stub)
Constructions/Quotients   → Core/Basic (stub)

Properties/*     → Core/Basic (stubs)
Theorems/*       → Core/Basic (stubs)
Examples/Standard → Core/Basic, Core/Objects, Constructions/Products
Examples/Counterexamples → Core/Basic (stub)
Bridges/*        → Core/Basic (stubs)
```
