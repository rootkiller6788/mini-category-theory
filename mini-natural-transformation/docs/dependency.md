# Mini Natural Transformation — Dependencies

## Required Packages

| Package | Path | Description |
|---------|------|-------------|
| mini-category-core | `../mini-category-core` | Category definitions (Category, Obj, Hom, comp, id) |
| mini-functor-core | `../mini-functor-core` | Functor definitions (Functor, mapObj, mapHom, preservesComp) |
| mini-morphism-system | `../mini-morphism-system` | Morphism infrastructure (SetCat, SetCatComponent) |

## Import Graph (23 submodules, all implemented)

```
MiniNaturalTransformation.lean (root aggregator)
├── Core/Basic            ← mini-category-core, mini-morphism-system
├── Core/Objects          ← Core/Basic, mini-category-core, mini-morphism-system
├── Core/Laws             ← Core/Basic, Core/Objects, mini-category-core, mini-morphism-system
├── Morphisms/Hom         ← Core/Basic, Core/Objects, Core/Laws
├── Morphisms/Iso         ← Core/Basic, Core/Objects, Core/Laws
├── Morphisms/Equivalence ← Core/Basic, Core/Objects, Morphisms/Iso
├── Constructions/Products    ← Core/Basic, Core/Objects
├── Constructions/Universal   ← Core/Basic, Core/Objects
├── Constructions/Subobjects  ← Core/Basic, Core/Objects
├── Constructions/Quotients   ← Core/Basic, Core/Objects
├── Properties/Invariants     ← Core/Basic, Core/Objects, Morphisms/Iso
├── Properties/Preservation   ← Core/Basic, Core/Objects, Morphisms/Iso, Properties/Invariants
├── Properties/ClassificationData ← Core/Basic, Core/Objects
├── Theorems/Basic            ← Core/Basic .. Morphisms/Iso
├── Theorems/UniversalProperties ← Core/Basic, Core/Objects
├── Theorems/Classification   ← Core/Basic .. Morphisms/Iso, Morphisms/Hom
├── Theorems/Main             ← Core/Basic .. Theorems/Basic, MiniFunctorCore
├── Examples/Standard         ← Core/Basic, Core/Objects, Morphisms/Iso
├── Examples/Counterexamples  ← Core/Basic, Core/Objects, Morphisms/Iso
├── Bridges/ToAlgebra         ← Core/Basic, Core/Objects
├── Bridges/ToTopology        ← Core/Basic, Core/Objects
├── Bridges/ToGeometry        ← Core/Basic, Core/Objects
└── Bridges/ToComputation     ← Core/Basic, Core/Objects
```

All submodules import from MiniCategoryCore and MiniMorphismSystem as needed.
Theorems/Main additionally imports MiniFunctorCore for Yoneda lemma constructions.
