# Dependencies

## Core Dependencies

- **mini-category-core** — Category, SetCat, Cᵒᵖ, C×D, DiscCat, CodiscCat
- **mini-functor-core** — Functor, Functor.id, Functor.comp
- **mini-natural-transformation** — NaturalTransformation, NaturalTransformation.vcomp
- **mini-adjunction** — Adjunction F ⊣ G

## Internal Dependencies

All modules import `MiniMonadCore.Core.Basic` which imports:
- `MiniCategoryCore.Core.Basic`
- `MiniMorphismSystem.Core.Basic`
- `MiniMorphismSystem.Core.Objects`
- `MiniNaturalTransformation.Core.Basic`
- `MiniNaturalTransformation.Core.Objects`

## Future Dependencies

This package is designed to be a foundation for:
- mini-comonad-core (comonads)
- mini-monad-transformer-core (monad transformers)
- mini-algebraic-effect-core (algebraic effects)
