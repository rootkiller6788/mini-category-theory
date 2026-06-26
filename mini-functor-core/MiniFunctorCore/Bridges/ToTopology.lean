/-
# MiniFunctorCore.Bridges.ToTopology

Stub module: bridges from functor theory to topology.
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

/-! ## Fundamental Groupoid as Functor -/

/--
The fundamental groupoid Π₁ : Top → Grpd is a functor.
-/
def fundamentalGroupoidFunctor : True := by
  trivial

/-! ## Simplicial Sets as Presheaves -/

/--
A simplicial set is a presheaf on the simplex category Δ.
-/
def simplicialSetAsPresheaf : True := by
  trivial

/-! ## Nerve of a Category -/

/--
The nerve N : Cat → sSet is a functor.
-/
def nerveAsFunctor : True := by
  trivial

/-! ## Classifying Space -/

/--
The classifying space B : Cat → Top is a functor.
-/
def classifyingSpaceFunctor : True := by
  trivial

#eval "Bridges.ToTopology: stub — fundamentalGroupoidFunctor, simplicialSetAsPresheaf, nerveAsFunctor, classifyingSpaceFunctor"
