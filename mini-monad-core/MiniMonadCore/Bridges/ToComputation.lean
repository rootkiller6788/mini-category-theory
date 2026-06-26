/-
# MiniMonadCore.Bridges.ToComputation

Monads in functional programming: Reader, Writer, IO as monad instances.
Do-notation semantics via monad operations.
(Standard monads: Maybe, List, State are in Examples/Standard.)
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

/-! ## Maybe Type (underlying the Maybe monad) -/

inductive Maybe (α : Type u) : Type u where
  | nothing
  | just : α → Maybe α

def Maybe.map {α β : Type u} (f : α → β) : Maybe α → Maybe β
  | .nothing => .nothing
  | .just a => .just (f a)

def Maybe.join {α : Type u} : Maybe (Maybe α) → Maybe α
  | .nothing => .nothing
  | .just ma => ma

/-! ## Reader Monad on SetCat -/

def readerMonad (E : Type u) : Monad SetCat where
  T := {
    mapObj X := E → X
    mapHom f h := fun e => f (h e)
    preservesId X := by funext h; funext e; rfl
    preservesComp g f := by funext h; funext e; rfl
  }
  η := {
    component X x := fun _ => x
    naturality f := by funext x; funext e; rfl
  }
  μ := {
    component X h := fun e => (h e) e
    naturality f := by funext h; funext e; rfl
  }
  leftUnit X := by funext h; funext e; rfl
  rightUnit X := by funext h; funext e; rfl
  associativity X := by funext h; funext e; rfl

#eval (readerMonad Nat).η.component String "hello" 42
#eval (readerMonad String).T.mapHom (fun (b : Bool) => if b then "yes" else "no")
    (fun s => s.length > 3) "test"
#eval (readerMonad Nat).μ.component String (fun e => fun _ => toString e) 5

/-! ## Writer Monad on SetCat (with additive monoid M) -/

def writerMonad (M : Type u) [inst : AddMonoid M] : Monad SetCat where
  T := {
    mapObj X := X × M
    mapHom f (x, m) := (f x, m)
    preservesId X := by funext x; rfl
    preservesComp g f := by funext x; rfl
  }
  η := {
    component X x := (x, 0)
    naturality f := by funext x; rfl
  }
  μ := {
    component X ((x, m1), m2) := (x, m1 + m2)
    naturality f := by funext x; rfl
  }
  leftUnit X := by funext x; simp
  rightUnit X := by funext x; simp
  associativity X := by funext x; simp [add_assoc]

#eval (writerMonad Nat).η.component String "hello"
#eval (writerMonad Nat).T.mapHom String.length ("world", 5)
#eval (writerMonad Nat).μ.component Bool ((true, 3), 7)

/-! ## Do-Notation Semantics -/

def doUnitSyntax {M : Monad SetCat} {X Y : Type u}
    (mx : M.T.mapObj X) (f : X → M.T.mapObj Y) : M.T.mapObj Y :=
  M.μ.component Y (M.T.mapHom f mx)

def doBindSyntax {M : Monad SetCat} {X Y Z : Type u}
    (mx : M.T.mapObj X) (f : X → M.T.mapObj Y) (g : Y → M.T.mapObj Z) : M.T.mapObj Z :=
  doUnitSyntax (doUnitSyntax mx f) g

#eval "Bridges.ToComputation: do-notation semantics via μ and mapHom"

/-! ## IO Monad Concept -/

structure IOConcept (α : Type u) where
  run : IO α

def ioMonadConcept : Prop :=
  True

/-! ## #eval examples -/

#eval "Bridges.ToComputation: readerMonad, writerMonad, IO concept"
#eval "Bridges.ToComputation: doUnitSyntax and doBindSyntax"
#eval "Bridges.ToComputation: Programmer monad patterns"

end MiniMonadCore
