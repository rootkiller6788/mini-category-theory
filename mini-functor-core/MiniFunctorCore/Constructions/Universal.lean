/-
# MiniFunctorCore.Constructions.Universal

Stub module: universal constructions in functor categories.
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

/-! ## Limits in Functor Categories -/

/--
Limits in a functor category [C, D] are computed pointwise
if D has limits.
-/
def limitsInFunctorCategory (C D : Category) : True := by
  trivial

/-! ## Colimits in Functor Categories -/

/--
Colimits in a functor category [C, D] are computed pointwise
if D has colimits.
-/
def colimitsInFunctorCategory (C D : Category) : True := by
  trivial

/-! ## Kan Extensions (stubs) -/

def leftKanExtension (C D E : Category) : True := by
  trivial

def rightKanExtension (C D E : Category) : True := by
  trivial

#eval "Constructions.Universal: stub — limitsInFunctorCategory, colimitsInFunctorCategory, leftKanExtension, rightKanExtension"
