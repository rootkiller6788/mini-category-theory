/-
# MiniMonadCore.Examples.Standard

Standard monad examples in SetCat: Maybe/Option, List, powerset, state monads.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Maybe/Option Monad on SetCat -/

def maybeMonad : Monad SetCat where
  T := {
    mapObj X := Option X
    mapHom f := Option.map f
    preservesId X := by
      funext x; cases x; rfl; rfl
    preservesComp g f := by
      funext x; cases x; rfl; rfl
  }
  η := {
    component := fun X x => some x
    naturality := fun f => by
      funext x; rfl
  }
  μ := {
    component := fun X oo =>
      match oo with
      | none => none
      | some o => o
    naturality := fun f => by
      funext oo;
      cases oo; rfl;
      case some o => rfl
  }
  leftUnit X := by
    funext x; induction x; rfl; rfl
  rightUnit X := by
    funext x; induction x; rfl; rfl
  associativity X := by
    funext x; induction x; rfl; case some o => induction o; rfl; rfl

#eval maybeMonad.η.component Nat 5
#eval maybeMonad.T.mapHom (fun (n : Nat) => n + 1) (some 3)
#eval maybeMonad.μ.component Nat (some (some 10))

/-! ## List Monad on SetCat -/

def listMonad : Monad SetCat where
  T := {
    mapObj X := List X
    mapHom f := List.map f
    preservesId X := by
      funext xs; simp
    preservesComp g f := by
      funext xs; simp
  }
  η := {
    component := fun X x => [x]
    naturality := fun f => by
      funext x; simp
  }
  μ := {
    component := fun X xss => List.join xss
    naturality := fun f => by
      funext xss; induction xss with
      | nil => rfl
      | cons xs xss ih =>
        simp [List.join, List.map, ih]
  }
  leftUnit X := by
    funext xs; induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  rightUnit X := by
    funext x; simp
  associativity X := by
    funext xsss; induction xsss with
    | nil => rfl
    | cons xss xsss ih =>
      simp [List.join, ih]

#eval listMonad.η.component String "hello"
#eval listMonad.T.mapHom (fun (s : String) => s ++ "!") ["a", "b"]
#eval listMonad.μ.component Nat [[1,2], [3], [], [4,5]]

/-! ## State Monad on SetCat -/

def stateMonad (S : Type u) : Monad SetCat where
  T := {
    mapObj X := S → X × S
    mapHom {X Y} f h := fun s =>
      match h s with
      | (x, s') => (f x, s')
    preservesId X := by
      funext h; funext s; rfl
    preservesComp {X Y Z} g f := by
      funext h; funext s; rfl
  }
  η := {
    component := fun X x s => (x, s)
    naturality := fun f => by
      funext x; funext s; rfl
  }
  μ := {
    component := fun X h s =>
      match h s with
      | (k, s') => k s'
    naturality := fun f => by
      funext h; funext s; rfl
  }
  leftUnit X := by
    funext h; funext s; rfl
  rightUnit X := by
    funext h; funext s; rfl
  associativity X := by
    funext h; funext s; rfl

def stateMonadNat : Monad SetCat := stateMonad Nat

#eval (stateMonadNat.η.component String "hello") 0
#eval (stateMonadNat.T.mapHom (fun (s : String) => s ++ "!") (fun (n : Nat) => (toString n, n+1))) 5
#eval (stateMonadNat.μ.component Bool (fun s => match s with
  | 0 => ((fun s' => (true, s'+1)), 10)
  | _ => ((fun s' => (false, s')), 7))) 0

/-! ## Powerset Monad sketch -/

def powersetFunctor : Functor SetCat SetCat where
  mapObj X := Set X
  mapHom f A := { y | ∃ x ∈ A, f x = y }
  preservesId X := by
    funext A; ext y; simp
  preservesComp g f := by
    funext A; ext z; simp

/-! ## #eval examples -/

#eval "Examples.Standard: maybeMonad, listMonad, stateMonad defined"
#eval "Examples.Standard: All three monads have #eval tests"
#eval "Examples.Standard: powersetFunctor sketch"

end MiniMonadCore
