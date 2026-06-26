/-
# MiniFunctorCore.Bridges.ToGeometry

Stub module: bridges from functor theory to geometry.
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

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Presheaves on a Topological Space -/

/--
Presheaves on a topological space X form the functor category [O(X)ᵒᵖ, Set]
where O(X) is the poset of open sets.
-/
def presheafOnSpace : True := by
  trivial

/-! ## Sites and Sheaves -/

/--
A site is a category with a Grothendieck topology; a sheaf is a presheaf
satisfying the gluing condition.
-/
def siteAndSheaf : True := by
  trivial

/-! ## Sheafification as Functor -/

/--
Sheafification is a left exact left adjoint to the forgetful functor
from sheaves to presheaves.
-/
def sheafificationFunctor : True := by
  trivial

/-! ## Functor of Points -/

/--
The functor of points approach to algebraic geometry:
a scheme is a functor Ring → Set.
-/
def functorOfPoints : True := by
  trivial

#eval "Bridges.ToGeometry: stub — presheafOnSpace, siteAndSheaf, sheafificationFunctor, functorOfPoints"
