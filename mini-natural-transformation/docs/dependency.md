# Mini Natural Transformation — Dependencies

## Required Packages

| Package | Path | Description |
|---------|------|-------------|
| mini-category-core | `../mini-category-core` | Category definitions (Category, Obj, Hom, comp, id) |
| mini-functor-core | `../mini-functor-core` | Functor definitions (Functor, mapObj, mapHom, preservesComp) |
| mini-morphism-system | `../mini-morphism-system` | Morphism infrastructure (SetCat, SetCatComponent) |

## Import Graph

```
MiniNaturalTransformation
├── Core/Basic       ← mini-category-core, mini-morphism-system
├── Core/Objects     ← Core/Basic
├── Core/Laws        ← Core/Basic
├── Morphisms/Hom    ← Core/Basic, Core/Objects
├── Morphisms/Iso    ← Core/Basic, Core/Objects
├── Morphisms/Equivalence ← Core/Basic
├── Constructions/*  ← Core/Basic
├── Properties/*     ← Core/Basic
├── Theorems/*       ← Core/Basic
├── Examples/*       ← Core/Basic
└── Bridges/*        ← Core/Basic
```
