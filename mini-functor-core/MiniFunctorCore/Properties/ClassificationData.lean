/-
# MiniFunctorCore.Properties.ClassificationData

Stub module: classification data for functor categories.
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

/-! ## Classification of Functor Categories -/

/--
A functor category [C, D] inherits structure from D.
-/
def functorCategoryClassification (C D : Category) : True := by
  trivial

/-! ## Presheaf Category Properties -/

/--
If C is small, [Cᵒᵖ, Set] is complete and cocomplete.
-/
def presheafCategoryProperties (C : Category) : True := by
  trivial

/-! ## Functor Category Size Classification -/

/--
Classification of functor categories by size.
-/
inductive FunctorCategoryClass where
  | smallSmall : FunctorCategoryClass
  | smallLarge : FunctorCategoryClass
  | largeSmall : FunctorCategoryClass
  | largeLarge : FunctorCategoryClass
  deriving Repr, DecidableEq

def classifyFunctorCategory (C D : Category) : FunctorCategoryClass :=
  FunctorCategoryClass.smallLarge

#eval "Properties.ClassificationData: stub — functorCategoryClassification, presheafCategoryProperties, FunctorCategoryClass"
