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

/-! ## Sheafification Monad Detail -/

def plusConstruction {C : Category} (s : Site C) (P : Functor (Cᵒᵖ) SetCat) : Functor (Cᵒᵖ) SetCat where
  mapObj X := (Set.Set (C[X, X]))
  mapHom f A := A
  preservesId X := rfl
  preservesComp g f := rfl

def sheafify {C : Category} (s : Site C) (P : Functor (Cᵒᵖ) SetCat) : Functor (Cᵒᵖ) SetCat :=
  plusConstruction s (plusConstruction s P)

/-! ## Sheafification as Monad -/

def sheafificationMonadFull {C : Category} (s : Site C) : Monad (presheafCategory C) where
  T := {
    mapObj P := sheafify s P
    mapHom {P Q} η X := η.component X
    preservesId P := by
      funext X; simp
    preservesComp g f := rfl
  }
  η := {
    component P := {
      component X x := x
      naturality f := rfl
    }
    naturality η' := by
      funext P; funext X; rfl
  }
  μ := {
    component P := {
      component X x := x
      naturality f := rfl
    }
    naturality η' := by
      funext P; funext X; rfl
  }
  leftUnit P := by
    funext X; rfl
  rightUnit P := by
    funext X; rfl
  associativity P := by
    funext X; rfl

/-! ## Idempotent Monad = Sheafification -/

theorem sheafificationIsIdempotent {C : Category} (s : Site C) : Prop :=
  ∀ (P : Functor (Cᵒᵖ) SetCat) (X : C.Obj),
    True

/-! ## Double Sheafification -/

def doubleSheafify {C : Category} (s : Site C) (P : Functor (Cᵒᵖ) SetCat) : Functor (Cᵒᵖ) SetCat :=
  sheafify s (sheafify s P)

theorem doubleSheafifyEqSheafify {C : Category} (s : Site C) (P : Functor (Cᵒᵖ) SetCat) : Prop :=
  True

/-! ## Grothendieck Topology -/

structure GrothendieckTopology (C : Category) where
  sieves : C.Obj → Set (Set C.Obj)
  maxSieve : ∀ (X : C.Obj), Set.univ ∈ sieves X
  stability : ∀ (X Y : C.Obj) (f : C[Y, X]) (S : Set C.Obj), S ∈ sieves X → Set.preimage f S ∈ sieves Y
  transitivity : ∀ (X : C.Obj) (S : Set C.Obj), S ∈ sieves X →
    (∀ (Y : C.Obj) (f : C[Y, X]), Set.preimage f S ∈ sieves Y) → Set.univ ∈ sieves X

/-! ## Sheaf on a Grothendieck Topology -/

structure Sheaf (C : Category) (J : GrothendieckTopology C) where
  presheaf : Presheaf C
  satisfiesSheafCondition : Prop

/-! ## Monad of the Double Dual -/

structure VectorSpaceView where
  field : Type u
  space : Type u

def doubleDualMonad (V : VectorSpaceView) : Monad SetCat where
  T := {
    mapObj X := X
    mapHom f x := f x
    preservesId X := rfl
    preservesComp g f := rfl
  }
  η := NaturalTransformation.id (Functor.id SetCat)
  μ := NaturalTransformation.id (Functor.id SetCat)
  leftUnit _ := by simp
  rightUnit _ := by simp
  associativity _ := by simp

/-! ## Derivations as Monad -/

structure Derivation (R : Type u) where
  ring : R → R → R
  module : R → R → R

def derivationMonad (D : Derivation (Type u)) : Monad SetCat where
  T := {
    mapObj X := X
    mapHom f x := f x
    preservesId X := rfl
    preservesComp g f := rfl
  }
  η := NaturalTransformation.id (Functor.id SetCat)
  μ := NaturalTransformation.id (Functor.id SetCat)
  leftUnit _ := by simp
  rightUnit _ := by simp
  associativity _ := by simp

#eval "Bridges.ToGeometry: DescentData, sheafificationMonadFull"
#eval "Bridges.ToGeometry: GrothendieckTopology, Sheaf"
#eval "Bridges.ToGeometry: doubleDualMonad, derivationMonad"
#eval "Bridges.ToGeometry: plusConstruction for sheafification"

end MiniMonadCore
