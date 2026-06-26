/-
# MiniAdjunction.Core.Basic

Adjunctions: the central concept in category theory.
An adjunction F ⊣ G between functors F : C → D and G : D → C.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Adjunction via Unit/Counit -/

structure Adjunction (C D : Category) (F : Functor C D) (G : Functor D C) where
  unit : Functor.id C ⇒ Functor.comp G F
  counit : Functor.comp F G ⇒ Functor.id D
  leftTriangle : ∀ (X : C.Obj),
    D.comp (counit.component (F.mapObj X)) (F.mapHom (unit.component X)) = D.id (F.mapObj X)
  rightTriangle : ∀ (Y : D.Obj),
    C.comp (G.mapHom (counit.component Y)) (unit.component (G.mapObj Y)) = C.id (G.mapObj Y)

notation:40 F:40 " ⊣ " G:40 => Adjunction F G

/-! ## Free/Forgetful Adjunction (concept) -/

structure FreeForgetful (C D : Category) where
  free : Functor C D
  forgetful : Functor D C
  adj : free ⊣ forgetful

#eval "Core.Basic: Adjunction F ⊣ G with unit/counit + triangle identities"
#eval "Core.Basic: Notation F ⊣ G for adjunctions"
#eval "Core.Basic: FreeForgetful structure (free ⊣ forgetful)"
