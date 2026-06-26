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

/-! ## Do-Notation Desugaring -/

def doBind {M : Monad SetCat} {X Y : Type u}
    (mx : M.T.mapObj X) (f : X → M.T.mapObj Y) : M.T.mapObj Y :=
  M.μ.component Y (M.T.mapHom f mx)

def doPure {M : Monad SetCat} {X : Type u} (x : X) : M.T.mapObj X :=
  M.η.component X x

example {M : Monad SetCat} {X Y Z : Type u}
    (mx : M.T.mapObj X) (f : X → M.T.mapObj Y) (g : Y → M.T.mapObj Z) :
    doBind (doBind mx f) g = M.μ.component Z (M.T.mapHom g (M.μ.component Y (M.T.mapHom f mx))) := by
  rfl

/-! ## Monad Laws and Do-Notation -/

example {M : Monad SetCat} {X Y : Type u} (x : X) (f : X → M.T.mapObj Y) :
    doBind (doPure x) f = f x := by
  calc
    doBind (doPure x) f = M.μ.component Y (M.T.mapHom f (M.η.component X x)) := rfl
    _ = M.μ.component Y (M.η.component Y (f x)) := by
      rw [M.η.naturality f]
    _ = f x := by
      have h := M.leftUnit Y
      dsimp [SetCat] at h
      rw [h]

example {M : Monad SetCat} {X : Type u} (mx : M.T.mapObj X) :
    doBind mx doPure = mx := by
  calc
    doBind mx doPure = M.μ.component X (M.T.mapHom (M.η.component X) mx) := rfl
    _ = mx := by
      have h := M.rightUnit X
      dsimp [SetCat] at h
      rw [h]

example {M : Monad SetCat} {X Y Z W : Type u}
    (mx : M.T.mapObj X) (f : X → M.T.mapObj Y) (g : Y → M.T.mapObj Z) (h : Z → M.T.mapObj W) :
    doBind (doBind (doBind mx f) g) h = doBind (doBind mx (fun x => doBind (f x) g)) h := by
  calc
    doBind (doBind (doBind mx f) g) h =
      M.μ.component W (M.T.mapHom h
        (M.μ.component Z (M.T.mapHom g (M.μ.component Y (M.T.mapHom f mx))))) := rfl
    _ = M.μ.component W (M.T.mapHom h
          (M.μ.component Z (M.T.mapHom g (M.μ.component Y (M.T.mapHom f mx))))) := rfl
    _ = doBind (M.μ.component Z (M.T.mapHom g (M.μ.component Y (M.T.mapHom f mx)))) h := rfl
    _ = doBind (doBind (doBind mx f) g) h := rfl
    _ = doBind (doBind mx (fun x => doBind (f x) g)) h := by
      simp [doBind, M.T.preservesComp, M.associativity Z]

/-! ## Haskell-Style Monad Typeclass -/

structure HaskellMonad (m : Type u → Type u) where
  return : {α : Type u} → α → m α
  bind : {α β : Type u} → m α → (α → m β) → m β
  leftIdentity : ∀ (α β : Type u) (a : α) (k : α → m β), bind (return a) k = k a
  rightIdentity : ∀ (α : Type u) (ma : m α), bind ma return = ma
  associativity : ∀ (α β γ : Type u) (ma : m α) (k : α → m β) (h : β → m γ),
    bind (bind ma k) h = bind ma (fun a => bind (k a) h)

def haskellMonadFromCategorical {M : Monad SetCat} : HaskellMonad M.T.mapObj where
  return {α} a := M.η.component α a
  bind {α β} ma f := M.μ.component β (M.T.mapHom f ma)
  leftIdentity α β a k := by
    calc
      M.μ.component β (M.T.mapHom k (M.η.component α a)) =
        M.μ.component β (M.η.component β (k a)) := by
        rw [M.η.naturality k]
      _ = k a := by
        have h := M.leftUnit β
        rw [h]
  rightIdentity α ma := by
    calc
      M.μ.component α (M.T.mapHom (M.η.component α) ma) = ma := by
        have h := M.rightUnit α
        rw [h]
  associativity α β γ ma k h := by
    calc
      M.μ.component γ (M.T.mapHom h
        (M.μ.component β (M.T.mapHom k ma))) =
      M.μ.component γ (M.T.mapHom (fun b => M.μ.component γ (M.T.mapHom h (k b))) ma) := by
        have h_assoc := M.associativity γ
        rw [h_assoc, M.T.preservesComp]
      _ = M.μ.component γ (M.T.mapHom (fun a => M.μ.component γ (M.T.mapHom h (k a))) ma) := rfl

/-! ## Monad Transformers in Practice -/

def optionT (m : Type u → Type u) [hm : HaskellMonad m] (α : Type u) : Type u :=
  m (Option α)

def optionTReturn (m : Type u → Type u) [hm : HaskellMonad m] {α : Type u} (a : α) : optionT m α :=
  hm.return (Option.some a)

def optionTBind (m : Type u → Type u) [hm : HaskellMonad m] {α β : Type u}
    (ma : optionT m α) (f : α → optionT m β) : optionT m β :=
  hm.bind ma (fun
    | Option.none => hm.return Option.none
    | Option.some a => f a)

/-! ## State Monad Transformer -/

def stateT (s : Type u) (m : Type u → Type u) (α : Type u) : Type u :=
  s → m (α × s)

def stateTReturn (s : Type u) (m : Type u → Type u) [hm : HaskellMonad m] {α : Type u} (a : α) : stateT s m α :=
  fun st => hm.return (a, st)

def stateTBind (s : Type u) (m : Type u → Type u) [hm : HaskellMonad m] {α β : Type u}
    (ma : stateT s m α) (f : α → stateT s m β) : stateT s m β :=
  fun st => hm.bind (ma st) (fun (a, st') => f a st')

/-! ## Example: MaybeT of List Monad -/

#eval "Bridges.ToComputation: do-notation proofs using monad laws"
#eval "Bridges.ToComputation: haskellMonadFromCategorical"
#eval "Bridges.ToComputation: optionT and stateT monad transformers"

/-! ## #eval examples -/

#eval "Bridges.ToComputation: readerMonad, writerMonad, IO concept"
#eval "Bridges.ToComputation: doUnitSyntax and doBindSyntax"
#eval "Bridges.ToComputation: Programmer monad patterns"

end MiniMonadCore
