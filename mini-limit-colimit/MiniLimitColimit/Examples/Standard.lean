/-
# MiniLimitColimit.Examples.Standard

Standard limits: products in SetCat, pullbacks in SetCat,
equalizers in SetCat, terminal/initial in SetCat.
Explicit computable examples.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Product in SetCat is Cartesian product -/

def setProductUnitBool : IsProduct SetCat Unit Bool (Unit × Bool) := {
  fst := Prod.fst
  snd := Prod.snd
  mediate := fun f g x => (f x, g x)
  fst_mediate := fun f g => rfl
  snd_mediate := fun f g => rfl
  unique := fun f g h h1 h2 => by
    funext x
    have hx1 : (fun y => Prod.fst (h y)) x = (f : SetCat[_, _]) x := congrFun h1 x
    have hx2 : (fun y => Prod.snd (h y)) x = (g : SetCat[_, _]) x := congrFun h2 x
    exact Prod.ext hx1 hx2
}

/-! ## Coproduct in SetCat is disjoint union -/

def setCoproductUnitBool : IsCoproduct SetCat Unit Bool (Sum Unit Bool) := {
  inl := Sum.inl
  inr := Sum.inr
  mediate := fun f g s => match s with
    | Sum.inl x => f x
    | Sum.inr x => g x
  inl_mediate := fun f g => rfl
  inr_mediate := fun f g => rfl
  unique := fun f g h h1 h2 => by
    funext x
    cases x with
    | inl x => exact congrFun h1 x
    | inr x => exact congrFun h2 x
}

/-! ## Equalizer in SetCat -/

def setEqualizerNatZero : Equalizer (SetCat := SetCat)
    (fun (n : Nat) => n) (fun (n : Nat) => 0) :=
  equalizerInSet (fun (n : Nat) => n) (fun (n : Nat) => 0)

def setEqualizerExample {A B : Type u} (f g : A → B) : Equalizer (SetCat := SetCat) f g :=
  equalizerInSet f g

/-! ## Coequalizer in SetCat -/

def setCoequalizerExample {A B : Type u} (f g : A → B) : Coequalizer (SetCat := SetCat) f g :=
  coequalizerInSet f g

/-! ## Pullback in SetCat: fiber product -/

def setPullbackExample {A B D : Type u} (f : A → D) (g : B → D) : Pullback (SetCat := SetCat) f g :=
  pullbackInSet f g

/-- Pullback of f : {0,1} → {0} and g : {0} → {0} -- the only map. -/
def setPullbackTrivial : Pullback (SetCat := SetCat)
    (fun (x : Fin 2) => (0 : Fin 1)) (fun (x : Fin 1) => (0 : Fin 1)) :=
  pullbackInSet (fun (x : Fin 2) => (0 : Fin 1)) (fun (x : Fin 1) => (0 : Fin 1))

/-! ## Pushout in SetCat -/

def setPushoutExample {A B X : Type u} (f : X → A) (g : X → B) : Pushout (SetCat := SetCat) f g :=
  pushoutInSet f g

/-! ## Limit of empty diagram = Terminal = Unit -/

/-- In SetCat, the terminal object is Unit. -/
def setTerminal : Terminal SetCat := {
  obj := Unit
  terminate _ := fun _ => ()
  unique X f := by
    funext x; simp
}

def setInitial : Initial SetCat := {
  obj := PEmpty
  initiate X := fun e => nomatch e
  unique X f := by
    funext x; exact nomatch x
}

/-! ## Product of three objects in SetCat -/

def productOfThreeInSet {A B C : Type u} : IsProduct SetCat (A × B) C ((A × B) × C) where
  fst x := x.1
  snd x := x.2
  mediate f g x := (f x, g x)
  fst_mediate f g := rfl
  snd_mediate f g := rfl
  unique f g h h1 h2 := by
    funext x
    have hx1 := congrFun h1 x
    have hx2 := congrFun h2 x
    exact Prod.ext hx1 hx2

/-! ## Infinite product (countable) as limit of discrete diagram -/

/-- An infinite sequence as an element of the product over Nat. -/
def productOfNats : Type := ∀ (n : Nat), Nat

def productOfNatsCone : Cone (Functor.const (DiscCat Nat) SetCat Nat) where
  apex := productOfNats
  proj n := fun x => x n
  naturality u := by simp

/-! ## #eval examples -/

#eval "Examples.Standard: Products, pullbacks, equalizers, terminal/initial in SetCat"
#eval setProductUnitBool.fst ((), true)
#eval setProductUnitBool.snd ((), false)
#eval setCoproductUnitBool.inl ()
#eval setTerminal.obj

end MiniLimitColimit
