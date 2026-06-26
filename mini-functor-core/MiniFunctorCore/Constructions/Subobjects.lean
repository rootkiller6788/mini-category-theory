/-
# MiniFunctorCore.Constructions.Subobjects

Stub module: subobjects in functor categories.
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

/-! ## Subfunctors -/

/--
A subfunctor of F : C → D is a functor S : C → D with a
monic natural transformation S ⇒ F.
-/
structure Subfunctor (C D : Category) (F : Functor C D) where
  S : Functor C D
  inclusion : S ⇒ F
  isMonic : ∀ (X : C.Obj), True := by trivial

/-! ## Subpresheaves -/

/--
A subpresheaf of a presheaf F : Cᵒᵖ → Set.
-/
def Subpresheaf (C : Category) (F : Functor (Cᵒᵖ) SetCat) :=
  Subfunctor (Cᵒᵖ) SetCat F

#eval "Constructions.Subobjects: stub — Subfunctor, Subpresheaf"
