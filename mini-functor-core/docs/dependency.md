# mini-functor-core -- Dependency Graph

## Internal Dependencies

```
Core/Basic.lean       (depends on mini-category-core, mini-morphism-system)
Core/Objects.lean     → Core/Basic
Core/Laws.lean        → Core/Basic, Core/Objects

Morphisms/Hom.lean    → Core/Basic, Core/Laws
Morphisms/Iso.lean    → Morphisms/Hom
Morphisms/Equivalence → Morphisms/Iso

Constructions/Products    → Morphisms/Hom, Morphisms/Iso
Constructions/Universal   → Morphisms/Hom
Constructions/Subobjects  → Morphisms/Hom
Constructions/Quotients   → Morphisms/Hom

Properties/Invariants       → Morphisms/Iso
Properties/Preservation     → Morphisms/Hom, Constructions/Products
Properties/ClassificationData → Constructions/Products

Theorems/Basic               → Properties/Invariants, Constructions/Products
Theorems/UniversalProperties → Morphisms/Iso, Constructions/Universal
Theorems/Classification      → Morphisms/Hom, Properties/ClassificationData
Theorems/Main                → Theorems/Basic, Theorems/UniversalProperties, Theorems/Classification

Examples/Standard       → Core/Basic, Morphisms/Hom, Morphisms/Iso
Examples/Counterexamples → Core/Basic, Properties/Invariants

Bridges/ToAlgebra       → Morphisms/Hom, Constructions/Products
Bridges/ToTopology      → Morphisms/Hom, Constructions/Products
Bridges/ToGeometry      → Morphisms/Hom, Constructions/Products
Bridges/ToComputation   → Morphisms/Hom, Constructions/Products
```

## External Dependencies

All modules depend on:
- `mini-category-core` (for Category, SetCat, opposite, product)
- `mini-morphism-system` (for Functor, NaturalTransformation)

Both are resolved via Lake relative paths from `../mini-category-core` and `../mini-morphism-system`.

## Import Graph (condensed)

```
mini-category-core ─┐
                     ├─ Core/Basic ← Core/Objects ← Core/Laws
mini-morphism-system─┘                ↓
                        ← Morphisms/Hom ← Morphisms/Iso ← Morphisms/Equivalence
                                ↓                ↓                ↓
                        ← Constructions/*  ←  Properties/*
                                ↓                ↓
                        ← Theorems/*  ←  Examples/*  ←  Bridges/*
```
