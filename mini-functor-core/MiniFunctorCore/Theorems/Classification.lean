/-
# MiniFunctorCore.Theorems.Classification

Stub module: classification of functor categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Constructions.Products
import MiniFunctorCore.Properties.Invariants
import MiniFunctorCore.Properties.ClassificationData

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Classification by Source Category -/

/--
Classification of functor categories [C, D] based on C.
-/
def classifyBySource (C D : Category) : True := by
  trivial

/-! ## Classification by Target Category -/

/--
The structure of [C, D] inherits from D.
-/
axiom functorCategoryInherits {C D : Category} (prop : Prop) : True

/-! ## Grothendieck Construction -/

/--
The Grothendieck construction: ∫ F is the category of elements of F.
-/
def grothendieckConstruction {C : Category} (F : Functor C SetCat) : True := by
  trivial

#eval "Theorems.Classification: stub — classifyBySource, functorCategoryInherits, grothendieckConstruction"
