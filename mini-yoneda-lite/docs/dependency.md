# mini-yoneda-lite Dependencies

## Direct Dependencies

```
mini-yoneda-lite
├── mini-category-core     (Category, SetCat, opposite, product, discrete, codiscrete)
│   └── mini-object-kernel (Axioms, Logic, Formula)
├── mini-functor-core      (Functor, homFunctor, identityFunctor, constantFunctor)
│   └── mini-category-core
│       └── mini-object-kernel
└── mini-natural-transformation (Natural transformation, functor category [C, D])
    ├── mini-category-core
    │   └── mini-object-kernel
    └── mini-functor-core
        └── mini-category-core
            └── mini-object-kernel
```

## Import Graph

```
MiniYonedaLite.lean (root aggregator)
├── MiniYonedaLite.Core.Basic
│   ├── MiniCategoryCore.Core.Basic
│   ├── MiniCategoryCore.Core.Objects
│   ├── MiniCategoryCore.Morphisms.Hom
│   ├── MiniCategoryCore.Morphisms.Iso
│   ├── MiniCategoryCore.Constructions.Products
│   ├── MiniFunctorCore.Core.Basic
│   ├── MiniFunctorCore.Morphisms.Hom
│   ├── MiniFunctorCore.Morphisms.Iso
│   ├── MiniFunctorCore.Theorems.Main
│   ├── MiniNaturalTransformation.Core.Basic
│   ├── MiniNaturalTransformation.Core.Objects
│   ├── MiniNaturalTransformation.Morphisms.Hom
│   ├── MiniNaturalTransformation.Morphisms.Iso
│   └── MiniNaturalTransformation.Theorems.Main
├── MiniYonedaLite.Core.Objects → MiniYonedaLite.Core.Basic
├── MiniYonedaLite.Theorems.Basic → MiniYonedaLite.Core.Basic
├── MiniYonedaLite.Theorems.Main → MiniYonedaLite.Core.Basic + .Theorems.Basic
├── MiniYonedaLite.Examples.Standard → MiniYonedaLite.Core.Basic + .Theorems.Basic + .Theorems.Main
└── (all stubs) → MiniYonedaLite.Core.Basic
```

## Upward Dependencies

- mini-everything-math (top-level package importing all sub-packages)
