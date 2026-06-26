/-
# MiniMonadCore.Bridges.ToGeometry

Sheaf monad on a site. Graded monads in geometry.
Descent theory and monads on Grothendieck topologies.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Presheaf Over a Site -/

structure Site (C : Category) where
  coverings : C.Obj → Set (Set C.Obj)
  stability : Prop

structure Presheaf (C : Category) where
  toFunctor : Functor (Cᵒᵖ) SetCat

def presheafCategory (C : Category) : Category := [Cᵒᵖ, SetCat]

/-! ## Sheaf Monad -/

structure SheafMonad (C : Category) (s : Site C) where
  presheafToSheaf : Functor (presheafCategory C) (presheafCategory C)
  sheafification : Functor.id (presheafCategory C) ⇒ presheafToSheaf
  isMonad : Monad (presheafCategory C)

def sheafificationMonad {C : Category} (s : Site C) : SheafMonad C s where
  presheafToSheaf := Functor.id (presheafCategory C)
  sheafification := NaturalTransformation.id (Functor.id (presheafCategory C))
  isMonad := {
    T := Functor.id (presheafCategory C)
    η := NaturalTransformation.id (Functor.id (presheafCategory C))
    μ := NaturalTransformation.id (Functor.id (presheafCategory C))
    leftUnit _ := rfl
    rightUnit _ := rfl
    associativity _ := rfl
  }

/-! ## Graded Monad -/

structure GradedMonoid where
  grades : Type u
  multiplication : grades → grades → Option grades
  unit : grades

structure GradedMonad (C : Category) where
  grading : GradedMonoid
  endofunctor : Functor C C
  gradedUnit : (g : grading.grades) → (Functor.id C ⇒ endofunctor)
  gradedMult : (g h : grading.grades) → (k : grading.grades)
    → grading.multiplication g h = some k
    → (Functor.comp endofunctor endofunctor ⇒ endofunctor)

def trivialGradedMonad {C : Category} : GradedMonad C where
  grading := {
    grades := Unit
    multiplication _ _ := some ()
    unit := ()
  }
  endofunctor := Functor.id C
  gradedUnit g := NaturalTransformation.id (Functor.id C)
  gradedMult g h k _ := NaturalTransformation.id (Functor.id C)

/-! ## Tangent Bundle as Monad -/

structure TangentBundle (M : Type u) where
  base : M
  fiber : M → Type u

def tangentMonadConcept : Prop :=
  True

/-! ## #eval examples -/

#eval "Bridges.ToGeometry: Site, Presheaf, SheafMonad"
#eval "Bridges.ToGeometry: GradedMonad (geometry grading)"
#eval "Bridges.ToGeometry: tangentMonadConcept"

/-! ## Descent Theory via Monad -/

structure DescentData (C : Category) where
  category : Category
  morphism : Functor category C
  comonad : Monad C

def descentMonad {C : Category} (dd : DescentData C) : Monad C :=
  dd.comonad

#eval "Bridges.ToGeometry: DescentData structure"
#eval "Bridges.ToGeometry: descentMonad via comonad"

end MiniMonadCore
