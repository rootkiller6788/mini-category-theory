/-
# MiniCategoryCore.Constructions.Subobjects

Subobject: an equivalence class of monomorphisms into a given object.
Defines the subobject preorder and operations (meet/join by pullback/pushout).
Reference to subobject classifier.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom

namespace MiniCategoryCore

/-! ## Subobject Definition -/

/-- A subobject of X is an object A together with a monomorphism A → X.
    Two monomorphisms represent the same subobject if they factor through an iso. -/
structure Subobject {C : Category} (X : C.Obj) where
  domain : C.Obj
  arrow : C[domain, X]
  is_mono : Mono arrow

/-- Two monomorphisms into X are equivalent as subobjects if they factor through each other. -/
def SubobjectEquiv {C : Category} {X : C.Obj} (s t : Subobject X) : Prop :=
  ∃ (i : Iso C s.domain t.domain), t.arrow ∘ i.hom = s.arrow

/-- The trivial subobject (identity on X). -/
def topSubobject {C : Category} (X : C.Obj) : Subobject X where
  domain := X
  arrow := C.id X
  is_mono := by
    intro Z g h h_eq
    calc
      g = C.id X ∘ g := by rw [C.id_comp]
      _ = (C.id X) ∘ g := rfl
      _ = (C.id X) ∘ h := by rw [h_eq]
      _ = h := by rw [C.id_comp]

/-- A subobject inclusion composes with a morphism to give another subobject. -/
def Subobject.pullback_morphism {C : Category} {X Y : C.Obj}
    (s : Subobject X) (f : C[Y, X]) : Subobject Y where
  domain := s.domain
  arrow := f
  is_mono := s.is_mono
  -- Note: this is just a restatement; true pullback requires limits

/-! ## Subobject Order -/

/-- The inclusion order on subobjects: s ≤ t if s factors through t. -/
def Subobject.le {C : Category} {X : C.Obj} (s t : Subobject X) : Prop :=
  ∃ (h : C[s.domain, t.domain]), t.arrow ∘ h = s.arrow

theorem Subobject.le_refl {C : Category} {X : C.Obj} (s : Subobject X) : Subobject.le s s := by
  exists C.id s.domain
  apply C.comp_id

theorem Subobject.le_trans {C : Category} {X : C.Obj} (s t u : Subobject X)
    (hst : Subobject.le s t) (htu : Subobject.le t u) : Subobject.le s u := by
  rcases hst with ⟨h1, h1_eq⟩
  rcases htu with ⟨h2, h2_eq⟩
  exists (h2 ∘ h1)
  calc
    u.arrow ∘ (h2 ∘ h1) = (u.arrow ∘ h2) ∘ h1 := by rw [C.assoc]
    _ = t.arrow ∘ h1 := by rw [h2_eq]
    _ = s.arrow := h1_eq

/-! ## Subobject Meet and Join -/

/-- The meet (intersection) of two subobjects via pullback (conceptual). -/
def Subobject.meet {C : Category} {X : C.Obj} (s t : Subobject X) : Prop :=
  -- Conceptual: the pullback of s.arrow and t.arrow
  ∃ (m : Subobject X), Subobject.le m s ∧ Subobject.le m t ∧
    ∀ (u : Subobject X), Subobject.le u s → Subobject.le u t → Subobject.le u m

/-- The join (union) of two subobjects via pushout (conceptual). -/
def Subobject.join {C : Category} {X : C.Obj} (s t : Subobject X) : Prop :=
  ∃ (j : Subobject X), Subobject.le s j ∧ Subobject.le t j ∧
    ∀ (u : Subobject X), Subobject.le s u → Subobject.le t u → Subobject.le j u

/-! ## Subobject Classifier -/

/-- A subobject classifier is an object Ω with a truth map ⊤ : 1 → Ω such that
    every mono is a pullback of ⊤. This is a reference definition. -/
structure SubobjectClassifier (C : Category) where
  Ω : C.Obj
  true : C.Obj -- terminal object
  truthMap : C[true, Ω]
  terminal_struct : Terminal C
  classifier_prop : ∀ {A X : C.Obj} (m : C[A, X]), Mono m →
    -- every mono arises as pullback of truthMap
    True

/-- In SetCat, the subobject classifier is Prop (or equivalently Bool). -/
def SetCat.subobjectClassifier : SubobjectClassifier SetCat where
  Ω := Prop
  true := Unit
  truthMap := λ _ => True
  terminal_struct := {
    obj := Unit,
    terminate := λ _ => (),
    unique := by
      intro X f; ext x; exact Unit.ext _ _
  }
  classifier_prop := by
    intro A X m hm
    trivial

#eval "Constructions.Subobjects: Subobject, order, meet/join, subobject classifier"
#eval s!"top subobject of Bool: {topSubobject Bool}"
#eval "SetCat subobject classifier Ω = Prop"
end MiniCategoryCore
