/-
# MiniFunctorCore.Properties.Preservation

Stub module: preservation properties in functor categories.
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

/-! ## Preservation of Functor Category Structure -/

/--
A functor preserves the functor category structure if it
maps natural transformations to natural transformations.
-/
def preservesFunctorCategory (F : Functor C D) : Prop := True

/-! ## Presheaf Preservation -/

/--
Properties of presheaf categories under base change.
-/
def presheafPreservation (C : Category) : True := by
  trivial

/-! ## Yoneda Preservation -/

/--
The Yoneda embedding preserves and reflects limits.
-/
def yonedaPreserves (C : Category) : True := by
  trivial

#eval "Properties.Preservation: stub — preservesFunctorCategory, presheafPreservation, yonedaPreserves"
