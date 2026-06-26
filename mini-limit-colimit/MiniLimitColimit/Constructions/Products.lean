/-
# MiniLimitColimit.Constructions.Products

Product and coproduct as limits/colimits over discrete 2-object diagrams.
Explicit constructions in SetCat.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Product as Limit over {0,1} discrete diagram -/

def productDiagram (C : Category) (A B : C.Obj) : Diagram (DiscCat (Fin 2)) C where
  mapObj
    | 0 => A
    | 1 => B
  mapHom f := by
    have : f.1.1.1 := Eq.refl _; exact C.id _
  preservesId _ := rfl
  preservesComp _ _ := by simp

structure IsProduct {C : Category} (A B P : C.Obj) where
  fst : C[P, A]
  snd : C[P, B]
  mediate : ∀ {Q : C.Obj}, C[Q, A] → C[Q, B] → C[Q, P]
  fst_mediate : ∀ {Q} (f : C[Q, A]) (g : C[Q, B]), C.comp fst (mediate f g) = f
  snd_mediate : ∀ {Q} (f : C[Q, A]) (g : C[Q, B]), C.comp snd (mediate f g) = g
  unique : ∀ {Q} (f : C[Q, A]) (g : C[Q, B]) (h : C[Q, P]),
    C.comp fst h = f → C.comp snd h = g → h = mediate f g

/-! ## Coproduct as Colimit -/

structure IsCoproduct {C : Category} (A B CProd : C.Obj) where
  inl : C[A, CProd]
  inr : C[B, CProd]
  mediate : ∀ {Q : C.Obj}, C[A, Q] → C[B, Q] → C[CProd, Q]
  inl_mediate : ∀ {Q} (f : C[A, Q]) (g : C[B, Q]), C.comp (mediate f g) inl = f
  inr_mediate : ∀ {Q} (f : C[A, Q]) (g : C[B, Q]), C.comp (mediate f g) inr = g
  unique : ∀ {Q} (f : C[A, Q]) (g : C[B, Q]) (h : C[CProd, Q]),
    C.comp h inl = f → C.comp h inr = g → h = mediate f g

/-! ## Product from IsProduct to Limit cone -/

def productAsCone {C : Category} {A B P : C.Obj} (prod : IsProduct A B P) : Cone (productDiagram C A B) where
  apex := P
  proj
    | 0 => prod.fst
    | 1 => prod.snd
  naturality u := by
    simp [productDiagram, DiscCat, C.id_comp]

def productAsLimit {C : Category} {A B P : C.Obj} (prod : IsProduct A B P) : Limit (productDiagram C A B) where
  limitCone := productAsCone prod
  mediate c := prod.mediate (c.proj 0) (c.proj 1)
  factor c j := by
    refine match j with
    | 0 => prod.fst_mediate (c.proj 0) (c.proj 1)
    | 1 => prod.snd_mediate (c.proj 0) (c.proj 1)
  unique c f h := by
    apply prod.unique (c.proj 0) (c.proj 1) f
    · have h0 := h 0
      simpa [productAsCone] using h0
    · have h1 := h 1
      simpa [productAsCone] using h1

/-! ## Coproduct from IsCoproduct to Colimit cocone -/

def coproductAsCocone {C : Category} {A B CP : C.Obj} (coprod : IsCoproduct A B CP) : Cocone (productDiagram C A B) where
  nadir := CP
  inj
    | 0 => coprod.inl
    | 1 => coprod.inr
  naturality u := by
    simp [productDiagram, DiscCat, C.comp_id]

def coproductAsColimit {C : Category} {A B CP : C.Obj} (coprod : IsCoproduct A B CP) : Colimit (productDiagram C A B) where
  colimitCocone := coproductAsCocone coprod
  mediate c := coprod.mediate (c.inj 0) (c.inj 1)
  factor c j := by
    refine match j with
    | 0 => coprod.inl_mediate (c.inj 0) (c.inj 1)
    | 1 => coprod.inr_mediate (c.inj 0) (c.inj 1)
  unique c f h := by
    apply coprod.unique (c.inj 0) (c.inj 1) f
    · have h0 := h 0
      simpa [coproductAsCocone] using h0
    · have h1 := h 1
      simpa [coproductAsCocone] using h1

/-! ## Finite products in SetCat -/

def productOfPairInSet {A B : Type u} : IsProduct (SetCat := SetCat) A B (A × B) where
  fst := Prod.fst
  snd := Prod.snd
  mediate f g x := (f x, g x)
  fst_mediate f g := rfl
  snd_mediate f g := rfl
  unique f g h h1 h2 := by
    funext x
    have hx1 : (fun y => Prod.fst (h y)) x = f x := congrFun h1 x
    have hx2 : (fun y => Prod.snd (h y)) x = g x := congrFun h2 x
    exact Prod.ext hx1 hx2

/-! ## Coproduct in SetCat -/

def coproductOfPairInSet {A B : Type u} : IsCoproduct (SetCat := SetCat) A B (A ⊕ B) where
  inl := Sum.inl
  inr := Sum.inr
  mediate f g s := match s with
    | Sum.inl a => f a
    | Sum.inr b => g b
  inl_mediate f g := rfl
  inr_mediate f g := rfl
  unique f g h h1 h2 := by
    funext x
    cases x with
    | inl a => exact congrFun h1 a
    | inr b => exact congrFun h2 b

/-! ## #eval examples -/

#eval "Constructions.Products: productAsLimit, coproductAsColimit"
#eval productOfPairInSet (A := Nat) (B := Bool) |>.fst (3, true)
#eval productOfPairInSet (A := Nat) (B := Bool) |>.snd (3, true)
#eval coproductOfPairInSet (A := String) (B := Nat) |>.inl "hello"

end MiniLimitColimit
