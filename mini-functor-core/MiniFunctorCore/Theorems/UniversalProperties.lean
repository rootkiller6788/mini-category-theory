/-
# MiniFunctorCore.Theorems.UniversalProperties

Stub module: universal properties in functor categories.
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
import MiniFunctorCore.Constructions.Universal

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Pointwise Kan Extensions -/

/--
Left Kan extensions exist when D is cocomplete (axiom).
-/
axiom leftKanExtensionExists {C D E : Category}
    (F : Functor C D) (G : Functor C E) [cocomplete : True] :
  Functor D E

/--
Right Kan extensions exist when D is complete (axiom).
-/
axiom rightKanExtensionExists {C D E : Category}
    (F : Functor C D) (G : Functor C E) [complete : True] :
  Functor D E

/-! ## Universal Property of Presheaf Category -/

/--
The presheaf category is the free cocompletion of C.
-/
axiom presheafFreeCocompletion {C : Category} :
  True

/-! ## Functor Category as Exponential -/

/--
The functor category provides a cartesian closed structure on Cat.
-/
def functorCategoryExponential (C D E : Category) : True := by
  trivial

#eval "Theorems.UniversalProperties: stub — leftKanExtensionExists, rightKanExtensionExists, presheafFreeCocompletion, functorCategoryExponential"
