/-
# MiniMorphismSystem.Morphisms.Iso

Functor isomorphisms and equivalence of categories.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Functor Isomorphism -/

structure FunctorIso {C D : Category} (F G : Functor C D) where
  component : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]
  inv : ∀ (X : C.Obj), D[G.mapObj X, F.mapObj X]
  leftInv : ∀ (X : C.Obj), D.comp (inv X) (component X) = D.id (F.mapObj X)
  rightInv : ∀ (X : C.Obj), D.comp (component X) (inv X) = D.id (G.mapObj X)

notation:50 F:50 " ≅ᶠ " G:50 => FunctorIso F G

/-! ## Equivalence of Categories -/

structure Equivalence (C D : Category) where
  forth : Functor C D
  back  : Functor D C
  unitIso  : Functor.id C ≅ᶠ Functor.comp back forth
  counitIso : Functor.comp forth back ≅ᶠ Functor.id D

#eval "Morphisms.Iso: FunctorIso, Equivalence of categories"
