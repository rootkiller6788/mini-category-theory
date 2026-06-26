# Dependencies

## Core Dependency

- **mini-object-kernel** — Object typeclass, TheoryName, Axiom system, Formula, Dependency graph

## Internal Dependencies

All modules import `MiniCategoryCore.Core.Basic` which imports:
- `MiniObjectKernel.Core.Basic`
- `MiniObjectKernel.Core.Objects`

## Future Dependencies

This package is designed to be a foundation for:
- mini-functor-core (functors, natural transformations)
- mini-limit-core (limits, colimits)
- mini-adjunction-core (adjunctions)
- mini-monad-core (monads)
