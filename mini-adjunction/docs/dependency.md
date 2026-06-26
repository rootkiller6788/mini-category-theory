# Dependencies

## Core Dependencies

- **mini-category-core** — Category structure, SetCat, opposite, product, discrete, codiscrete categories
- **mini-functor-core** — Functor categories [C, D], hom-functors, evaluation functors, slice/coslice
- **mini-natural-transformation** — Natural transformations F ⇒ G, vertical and horizontal composition

## Internal Dependencies

All modules import `MiniAdjunction.Core.Basic` which imports:
- `MiniCategoryCore.Core.Basic`
- `MiniCategoryCore.Core.Laws`
- `MiniMorphismSystem.Core.Basic`
- `MiniMorphismSystem.Core.Objects`
- `MiniNaturalTransformation.Core.Basic`
- `MiniNaturalTransformation.Core.Objects`

## Future Dependencies

This package is designed to be a foundation for:
- mini-limit-core (limits, colimits, adjoint functor theorems)
- mini-monad-core (monads from adjunctions)
- mini-kan-extension-core (Kan extensions)
