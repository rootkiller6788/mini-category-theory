# mini-limit-colimit -- Dependency Graph

## Internal Dependencies

```
Core/Basic.lean       (depends on: mini-category-core, mini-morphism-system)
Core/Objects.lean     → Core/Basic
Core/Laws.lean        → Core/Basic, Core/Objects

Morphisms/Hom.lean    → Core/Basic, mini-functor-core, mini-natural-transformation
Morphisms/Iso.lean    → Core/Basic
Morphisms/Equivalence → Core/Basic

Constructions/Products.lean    → Core/Basic, Core/Objects
Constructions/Universal.lean   → Core/Basic, Core/Objects, mini-category-core
Constructions/Subobjects.lean  → Core/Basic
Constructions/Quotients.lean   → Core/Basic

Properties/Invariants.lean       → Core/Basic
Properties/Preservation.lean     → Core/Basic
Properties/ClassificationData.lean → Core/Basic

Theorems/Basic.lean               → Core/Basic
Theorems/UniversalProperties.lean → Core/Basic
Theorems/Classification.lean      → Core/Basic
Theorems/Main.lean                → Core/Basic

Examples/Standard.lean       → Core/Basic, Core/Objects, Constructions/Products
Examples/Counterexamples.lean → Core/Basic

Bridges/ToAlgebra.lean       → Core/Basic
Bridges/ToTopology.lean      → Core/Basic
Bridges/ToGeometry.lean      → Core/Basic
Bridges/ToComputation.lean   → Core/Basic
```

## External Dependencies

- `mini-category-core` — Category, SetCat, DiscCat, CodiscCat, Terminal, Initial
- `mini-functor-core` — Functor, Functor.const
- `mini-natural-transformation` — natural transformations for morphisms of cones

## Import Graph (condensed)

```
mini-category-core ─┐
mini-morphism-system┼──→ Core/Basic ──→ Core/Objects ──→ Core/Laws
mini-functor-core ──┤                            ↓
mini-nat-trans ─────┘    ──→ Morphisms/Hom
                              ↓
                    ──→ Constructions/Products
                    ──→ Constructions/Universal
                              ↓
                    ──→ Properties/*  (stubs)
                              ↓
                    ──→ Theorems/*  (stubs)
                              ↓
                    ──→ Examples/*  ──→ Bridges/*  (stubs)
```
