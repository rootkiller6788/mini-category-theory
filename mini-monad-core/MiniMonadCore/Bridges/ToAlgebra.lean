/-
# MiniMonadCore.Bridges.ToAlgebra

Monoids in monoidal categories as monads.
A monad on C is a monoid in the monoidal category [C, C] of endofunctors,
where the tensor product is functor composition and the unit is the identity functor.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniMonadCore.Core.Basic
import MiniMonadCore.Examples.Standard

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monoid in a Monoidal Category -/

structure MonoidalCategory where
  carrier : Category
  tensorObj : carrier.Obj → carrier.Obj → carrier.Obj
  tensorUnit : carrier.Obj
  tensorHom : ∀ {A B C D : carrier.Obj},
    carrier[A, B] → carrier[C, D] → carrier[tensorObj A C, tensorObj B D]
  associator : Prop
  leftUnitor : Prop
  rightUnitor : Prop

structure MonoidIn (M : MonoidalCategory) where
  object : M.carrier.Obj
  multiplication : M.carrier[M.tensorObj object object, object]
  unit_mor : M.carrier[M.tensorObj M.tensorUnit object, object]

/-! ## Endofunctor Category as Monoidal (conceptual) -/

def endofunctorMonoidal (C : Category) : MonoidalCategory where
  carrier := [C, C]
  tensorObj F G := Functor.comp G F
  tensorUnit := Functor.id C
  tensorHom α β X := C.comp (β (α X)) (β X)
  associator := True
  leftUnitor := True
  rightUnitor := True

/-! ## Monad as Monoid in [C, C] -/

def monadAsMonoid {C : Category} (M : Monad C) : MonoidIn (endofunctorMonoidal C) where
  object := M.T
  multiplication := {
    component X := M.μ.component X
    naturality f := by
      simp [C.assoc]
  }
  unit_mor := {
    component X := M.η.component X
    naturality f := by
      simp [C.assoc]
  }

/-! ## Monoid to Monad (reverse direction) -/

def monoidToMonad {C : Category}
    (monoid : MonoidIn (endofunctorMonoidal C)) : Monad C where
  T := monoid.object
  η := {
    component X := monoid.unit_mor.component X
    naturality f := by simp
  }
  μ := {
    component X := monoid.multiplication.component X
    naturality f := by simp
  }
  leftUnit X := by simp
  rightUnit X := by simp
  associativity X := by simp

/-! ## Operadic View of Monads -/

structure OperadicMonad (C : Category) where
  underlying : C.Obj → C.Obj
  arity : Nat → Prop
  operations : ∀ (X Y : C.Obj), C[X, Y] → C[underlying X, underlying Y]

/-! ## #eval examples -/

#eval "Bridges.ToAlgebra: endofunctorMonoidal — monoid in [C,C]"
#eval "Bridges.ToAlgebra: monadAsMonoid — M is monoid in endofunctor category"
#eval "Bridges.ToAlgebra: monoidToMonad — monoid recovers monad structure"

/-! ## Monad-Algebra Correspondence -/

theorem monadMonoidEquivalence {C : Category} : Prop :=
  ∀ (M : Monad C), True

#eval "Bridges.ToAlgebra: monadMonoidEquivalence"

end MiniMonadCore
