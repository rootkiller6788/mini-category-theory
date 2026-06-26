/-
# MiniMonadCore.Core.Basic

Monad on a category C: an endofunctor T : C → C with
unit η : 1_C ⇒ T and multiplication μ : T² ⇒ T satisfying the monad laws.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad -/

structure Monad (C : Category) where
  T : Functor C C
  η : Functor.id C ⇒ T
  μ : Functor.comp T T ⇒ T
  leftUnit : ∀ (X : C.Obj),
    C.comp (μ.component X) (η.component (T.mapObj X)) = C.id (T.mapObj X)
  rightUnit : ∀ (X : C.Obj),
    C.comp (μ.component X) (T.mapHom (η.component X)) = C.id (T.mapObj X)
  associativity : ∀ (X : C.Obj),
    C.comp (μ.component X) (μ.component (T.mapObj X)) = C.comp (μ.component X) (T.mapHom (μ.component X))

/-! ## Monad Morphism -/

structure MonadMorphism {C : Category} (M N : Monad C) where
  component : M.T ⇒ N.T
  unitCompat : ∀ (X : C.Obj),
    C.comp (component.component X) (M.η.component X) = N.η.component X
  multCompat : ∀ (X : C.Obj),
    C.comp (component.component X) (M.μ.component X) =
    C.comp (N.μ.component X) (NaturalTransformation.vcomp (component) (component)).component X

#eval "Core.Basic: Monad (T, η, μ), MonadMorphism"
