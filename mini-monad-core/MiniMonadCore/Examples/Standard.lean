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

/-! ## Reader Monad on SetCat -/

def readerMonadExample (E : Type u) : Monad SetCat where
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

#eval (readerMonadExample Nat).η.component String "hello" 42
#eval (readerMonadExample String).μ.component Int (fun e => fun _ => e.length) "test"

/-! ## Writer Monad on SetCat -/

def writerMonadExample (M : Type u) [AddMonoid M] : Monad SetCat where
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

#eval (writerMonadExample Nat).η.component String "hello"
#eval (writerMonadExample Nat).μ.component Bool ((true, 3), 7)

/-! ## Exception Monad on SetCat -/

def exceptionMonad (E : Type u) : Monad SetCat where
  T := {
    mapObj X := Sum E X
    mapHom f
      | Sum.inl e => Sum.inl e
      | Sum.inr x => Sum.inr (f x)
    preservesId X := by
      funext s; cases s; rfl; rfl
    preservesComp g f := by
      funext s; cases s; rfl; rfl
  }
  η := {
    component X x := Sum.inr x
    naturality f := by funext x; rfl
  }
  μ := {
    component X
      | Sum.inl e => Sum.inl e
      | Sum.inr (Sum.inl e) => Sum.inl e
      | Sum.inr (Sum.inr x) => Sum.inr x
    naturality f := by
      funext s; cases s; rfl; case inr s' => cases s'; rfl; rfl
  }
  leftUnit X := by
    funext s; cases s; rfl; rfl
  rightUnit X := by
    funext s; cases s; rfl; rfl
  associativity X := by
    funext s; cases s; rfl; case inr s' =>
      cases s'; rfl; case inr s'' =>
        cases s''; rfl; rfl

#eval (exceptionMonad String).η.component Nat 42
#eval (exceptionMonad String).μ.component Int (Sum.inr (Sum.inr 10))

/-! ## Free Monad on a Functor -/

inductive FreeMonadTree (F : Type u → Type u) (X : Type u) : Type u where
  | pure : X → FreeMonadTree F X
  | impure : F (FreeMonadTree F X) → FreeMonadTree F X

def freeMonad (F : Functor SetCat SetCat) : Monad SetCat where
  T := {
    mapObj X := FreeMonadTree F.mapObj X
    mapHom {X Y} f
      | FreeMonadTree.pure x => FreeMonadTree.pure (f x)
      | FreeMonadTree.impure fx =>
        FreeMonadTree.impure (F.mapHom (mapHom F f) fx)
    preservesId X := by
      funext t; induction t with
      | pure x => rfl
      | impure fx ih =>
        simp [mapHom, F.preservesId, ih]
    preservesComp {X Y Z} g f := by
      funext t; induction t with
      | pure x => rfl
      | impure fx ih =>
        simp [mapHom, F.preservesComp, ih]
  }
  η := {
    component X x := FreeMonadTree.pure x
    naturality f := by funext x; rfl
  }
  μ := {
    component X t := joinFree F X t
    naturality f := by
      funext t; induction t with
      | pure x => rfl
      | impure fx ih =>
        simp [F.preservesComp, mapHom, ih]
  }
  leftUnit X := by
    funext t; induction t with
    | pure x => rfl
    | impure fx ih => simp [F.preservesId, mapHom, ih]
  rightUnit X := by
    funext t; induction t with
    | pure x => rfl
    | impure fx ih => simp [F.preservesId, mapHom, ih]
  associativity X := by
    funext t; induction t with
    | pure x => rfl
    | impure fx ih => simp [F.preservesComp, F.preservesId, mapHom, ih]
where
  mapHom (F : Functor SetCat SetCat) {X Y : Type u} (f : X → Y) : FreeMonadTree F.mapObj X → FreeMonadTree F.mapObj Y
    | FreeMonadTree.pure x => FreeMonadTree.pure (f x)
    | FreeMonadTree.impure fx => FreeMonadTree.impure (F.mapHom (mapHom F f) fx)
  joinFree (F : Functor SetCat SetCat) (X : Type u) : FreeMonadTree F.mapObj (FreeMonadTree F.mapObj X) → FreeMonadTree F.mapObj X
    | FreeMonadTree.pure t => t
    | FreeMonadTree.impure ft =>
      FreeMonadTree.impure (F.mapHom (joinFree F X) ft)

#eval "Examples.Standard: freeMonad on a functor F"

/-! ## Continuation Monad on SetCat -/

def contMonad (R : Type u) : Monad SetCat where
  T := {
    mapObj X := (X → R) → R
    mapHom {X Y} f h := fun k => h (fun x => k (f x))
    preservesId X := by funext h; rfl
    preservesComp g f := by funext h; rfl
  }
  η := {
    component X x := fun k => k x
    naturality f := by funext x; rfl
  }
  μ := {
    component X h := fun k => h (fun f => f k)
    naturality f := by funext h; rfl
  }
  leftUnit X := by funext h; rfl
  rightUnit X := by funext h; rfl
  associativity X := by funext h; rfl

#eval (contMonad Nat).η.component Bool true (fun b => if b then 1 else 0)
#eval (contMonad String).μ.component Int (fun k => k (fun n => if n > 0 then "pos" else "nonpos")) id

/-! ## Tree Monad on SetCat -/

inductive Tree (X : Type u) : Type u where
  | leaf : X → Tree X
  | node : List (Tree X) → Tree X

def Tree.map {X Y : Type u} (f : X → Y) : Tree X → Tree Y
  | Tree.leaf x => Tree.leaf (f x)
  | Tree.node ts => Tree.node (List.map (Tree.map f) ts)

def Tree.join {X : Type u} : Tree (Tree X) → Tree X
  | Tree.leaf t => t
  | Tree.node tts => Tree.node (List.map Tree.join tts)

def treeMonad : Monad SetCat where
  T := {
    mapObj X := Tree X
    mapHom f := Tree.map f
    preservesId X := by
      funext t; induction t with
      | leaf x => rfl
      | node ts ih => simp [Tree.map, ih]
    preservesComp g f := by
      funext t; induction t with
      | leaf x => rfl
      | node ts ih => simp [Tree.map, ih]
  }
  η := {
    component X x := Tree.leaf x
    naturality f := by funext x; rfl
  }
  μ := {
    component X := Tree.join
    naturality f := by
      funext t; induction t with
      | leaf t' => rfl
      | node ts ih => simp [Tree.join, Tree.map, ih]
  }
  leftUnit X := by
    funext t; induction t with
    | leaf x => rfl
    | node ts ih => simp [Tree.join, Tree.map, ih]
  rightUnit X := by
    funext x; rfl
  associativity X := by
    funext t; induction t with
    | leaf t' => rfl
    | node ts ih => simp [Tree.join, Tree.map, ih]

#eval treeMonad.η.component Nat 5
#eval treeMonad.μ.component String (Tree.node [Tree.leaf (Tree.leaf "a"), Tree.leaf (Tree.leaf "b")])

#eval "Examples.Standard: contMonad, treeMonad, exceptionMonad"
#eval "Examples.Standard: freeMonad construction"

end MiniMonadCore
