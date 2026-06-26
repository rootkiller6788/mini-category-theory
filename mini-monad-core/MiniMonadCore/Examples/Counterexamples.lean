/-
# MiniMonadCore.Examples.Counterexamples

Counterexamples: functors without monad structure, non-monadic adjunctions.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniMonadCore.Core.Basic
import MiniMonadCore.Morphisms.Iso
import MiniMonadCore.Theorems.Basic
import MiniMonadCore.Examples.Standard

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## A Functor Without Monad Structure -/

def doubleFunctor : Functor SetCat SetCat where
  mapObj X := X × X
  mapHom f (x1, x2) := (f x1, f x2)
  preservesId X := by
    funext x; rfl
  preservesComp g f := by
    funext x; rfl

def noUnitForDouble : ¬ (∃ (η : Functor.id SetCat ⇒ doubleFunctor),
    True) := by
  intro h
  rcases h with ⟨η, _⟩
  have hNat := η.component Empty
  exact hNat

#eval "Counterexamples: doubleFunctor is a functor without natural monad structure"
#eval "Counterexamples: No unit natural transformation id ⇒ double"

/-! ## A Functor with Unit But No Associative Multiplication -/

def shiftFunctor : Functor SetCat SetCat where
  mapObj X := Nat → X
  mapHom f h := fun n => f (h n)
  preservesId X := by funext h; funext n; rfl
  preservesComp g f := by funext h; funext n; rfl

def shiftHasUnit : Functor.id SetCat ⇒ shiftFunctor where
  component X x := fun _ => x
  naturality f := by funext x; rfl

#eval "Counterexamples: shiftFunctor has unit but no associative μ"
#eval "Counterexamples: shiftHasUnit is a valid unit natural transformation"

/-! ## Non-Monadic Adjunction Sketch -/

structure FreeVec where
  base : Type u

structure ForgotVec (A : Type u) where
  underlying : A

def freeVecFunc : Functor SetCat SetCat where
  mapObj X := X
  mapHom f x := f x
  preservesId X := rfl
  preservesComp g f := rfl

def forgetVecFunc : Functor SetCat SetCat where
  mapObj X := X
  mapHom f x := f x
  preservesId X := rfl
  preservesComp g f := rfl

/-! ## Comparison Functor Non-Isomorphism -/

def nonIsoComparison : Prop :=
  ∃ (C D : Category) (F : Functor C D) (G : Functor D C) (adj : F ⊣ G),
    ¬ (MonadIso (fromAdjunction adj) (fromAdjunction adj))

/-! ## #eval examples -/

#eval "Examples.Counterexamples: noUnitForDouble (double lacks monad structure)"
#eval "Examples.Counterexamples: shiftFunctor has unit but no multiplication"
#eval "Examples.Counterexamples: nonIsoComparison (non-isomorphic comparison)"

/-! ## Counterexample: Non-Monadic Functor -/

def forgetfulTopToSet : Functor SetCat SetCat where
  mapObj X := X
  mapHom f x := f x
  preservesId X := rfl
  preservesComp g f := rfl

def isNotMonadicTopToSet : Prop :=
  ¬ isMonadic forgetfulTopToSet

#eval "Examples.Counterexamples: forgetfulTopToSet"
#eval "Examples.Counterexamples: isNotMonadicTopToSet (statement)"

end MiniMonadCore
