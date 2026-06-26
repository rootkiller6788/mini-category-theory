# mini-monad-core

Monad theory: Monad (T, η, μ), Kleisli category, Eilenberg-Moore category, monad laws.

## Contents

- `Core/Basic.lean` — Monad structure (endofunctor T, unit η, multiplication μ), MonadMorphism
- `Core/Objects.lean` — Kleisli category construction Kl(M)
- `Core/Laws.lean` — Monad laws (left unit, right unit, associativity)
- `Constructions/Universal.lean` — Eilenberg-Moore algebra and category
- `Theorems/Basic.lean` — Every adjunction induces a monad
- `Bridges/ToComputation.lean` — Monads in functional programming (Maybe, List)

## Dependencies

- `mini-category-core` (for Category, SetCat)
- `mini-functor-core` (for Functor)
- `mini-natural-transformation` (for NaturalTransformation)
- `mini-adjunction` (for Adjunction → Monad theorem)
