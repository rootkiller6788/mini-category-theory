/-
# MiniFunctorCore.Constructions.Quotients

Stub module: quotients in functor categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Quotient Functors -/

/--
A quotient of a functor F : C → D by a natural congruence.
-/
structure QuotientFunctor (C D : Category) (F : Functor C D) where
  Q : Functor C D
  projection : F ⇒ Q
  isEpic : ∀ (X : C.Obj), True := by trivial

/-! ## Coequalizers in Functor Categories -/

/--
Coequalizers in functor categories are computed pointwise.
-/
def coequalizerInFunctorCategory (C D : Category) : True := by
  trivial

#eval "Constructions.Quotients: stub — QuotientFunctor, coequalizerInFunctorCategory"
