/-
# MiniFunctorCore.Bridges.ToAlgebra

Stub module: bridges from functor theory to algebra.
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

/-! ## Modules as Functors -/

/--
A module over a ring R can be viewed as an additive functor
from the one-object category of R to Ab.
-/
def moduleAsFunctor : True := by
  trivial

/-! ## Group Actions as Functors -/

/--
A G-set is a functor from the one-object category BG to Set.
-/
def groupActionAsFunctor (G : Type u) : True := by
  trivial

/-! ## Representations as Functors -/

/--
A representation of a group G is a functor BG → Vect.
-/
def representationAsFunctor : True := by
  trivial

/-! ## Algebras over a Monad -/

/--
An algebra over a monad T is an Eilenberg-Moore algebra.
-/
def algebraOverMonad : True := by
  trivial

#eval "Bridges.ToAlgebra: stub — moduleAsFunctor, groupActionAsFunctor, representationAsFunctor, algebraOverMonad"
