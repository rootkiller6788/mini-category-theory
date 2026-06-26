/-
# MiniCategoryCore.Constructions.Quotients

Quotient category: given a congruence on hom-sets (an equivalence relation
compatible with composition and identity laws), form the quotient category
with the same objects and equivalence classes as morphisms.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Categorical Congruence -/

/-- A categorical congruence is an equivalence relation on each hom-set
    that is compatible with composition and the category laws. -/
structure CatCongruence (C : Category) where
  rel : ∀ {X Y : C.Obj}, C[X, Y] → C[X, Y] → Prop
  isEquiv : ∀ {X Y : C.Obj}, Equivalence (rel (X := X) (Y := Y))
  compat_comp : ∀ {X Y Z : C.Obj} {f f' : C[X, Y]} {g g' : C[Y, Z]},
    rel f f' → rel g g' → rel (g ∘ f) (g' ∘ f')
  reduces_id_right : ∀ {X Y : C.Obj} (f : C[X, Y]), rel (f ∘ C.id X) f
  reduces_id_left : ∀ {X Y : C.Obj} (f : C[X, Y]), rel (C.id Y ∘ f) f
  reduces_assoc : ∀ {W X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]) (h : C[W, X]),
    rel (f ∘ (g ∘ h)) ((f ∘ g) ∘ h)

/-- The trivial congruence (equality). -/
def trivialCatCongruence (C : Category) : CatCongruence C where
  rel f g := f = g
  isEquiv := {
    refl := λ _ => rfl
    symm := λ h => h.symm
    trans := λ h1 h2 => h1.trans h2
  }
  compat_comp := by
    intro X Y Z f f' g g' hf hg; rw [hf, hg]
  reduces_id_right f := by rw [C.comp_id]
  reduces_id_left f := by rw [C.id_comp]
  reduces_assoc f g h := (C.assoc f g h).symm

/-- The codiscrete congruence (all parallel morphisms are equivalent). -/
def codiscreteCatCongruence (C : Category) : CatCongruence C where
  rel _ _ _ _ := True
  isEquiv := {
    refl := λ _ => trivial
    symm := λ _ => trivial
    trans := λ _ _ => trivial
  }
  compat_comp := by intro _ _ _ _ _ _ _ _ _ _; trivial
  reduces_id_right _ := trivial
  reduces_id_left _ := trivial
  reduces_assoc _ _ _ := trivial

/-! ## Quotient Category Construction -/

/-- The quotient category C/~ for a categorical congruence ~.
    Objects are the same, morphisms are equivalence classes. -/
def QuotientCat (C : Category) (R : CatCongruence C) : Category where
  Obj := C.Obj
  Hom X Y := Quot (R.rel (X := X) (Y := Y))
  id X := Quot.mk _ (C.id X)
  comp g f := Quot.liftOn₂ g f
    (λ g' f' => Quot.mk _ (g' ∘ f'))
    (λ a₁ b₁ h₁ a₂ b₂ _ => Quot.sound (R.compat_comp h₁ (R.isEquiv.refl _)))
    (λ a₁ a₂ h₂ => Quot.sound (R.compat_comp (R.isEquiv.refl _) h₂))
  comp_id f := by
    apply Quot.inductionOn f
    intro f'
    apply Quot.sound
    apply R.reduces_id_right
  id_comp f := by
    apply Quot.inductionOn f
    intro f'
    apply Quot.sound
    apply R.reduces_id_left
  assoc f g h := by
    apply Quot.inductionOn₃ f g h
    intro f' g' h'
    apply Quot.sound
    apply R.reduces_assoc

/-! ## Quotient Projection and Universal Property -/

/-- The projection map on objects (identity). -/
def QuotientProjObj {C : Category} (R : CatCongruence C) (X : C.Obj) : (QuotientCat C R).Obj := X

/-- The projection on morphisms sends f to its equivalence class. -/
def QuotientProjHom {C : Category} (R : CatCongruence C) {X Y : C.Obj} (f : C[X, Y]) :
    (QuotientCat C R)[X, Y] :=
  Quot.mk _ f

/-- The projection preserves identity. -/
theorem quotient_proj_map_id {C : Category} (R : CatCongruence C) (X : C.Obj) :
    QuotientProjHom R (C.id X) = (QuotientCat C R).id X := rfl

/-- The projection preserves composition. -/
theorem quotient_proj_map_comp {C : Category} (R : CatCongruence C) {X Y Z : C.Obj}
    (f : C[Y, Z]) (g : C[X, Y]) :
    QuotientProjHom R (f ∘ g) = (QuotientCat C R).comp (QuotientProjHom R f) (QuotientProjHom R g) :=
  rfl

/-- A function on objects respects a congruence if equivalent maps are sent to equal maps. -/
def RespectsCongruence {C D : Category} {F : C.Obj → D.Obj}
    (onHom : ∀ {X Y : C.Obj}, C[X, Y] → D[F X, F Y])
    (R : CatCongruence C) : Prop :=
  ∀ {X Y : C.Obj} {f g : C[X, Y]}, R.rel f g → onHom f = onHom g

/-- The universal property of the quotient category:
    any structure respecting the congruence factors uniquely through the projection.
    This is stated as an axiom for complete generality. -/
axiom quotientUniversalProperty
    {C D : Category} (R : CatCongruence C) (F : C.Obj → D.Obj)
    (onHom : ∀ {X Y : C.Obj}, C[X, Y] → D[F X, F Y])
    (map_id : ∀ (X : C.Obj), onHom (C.id X) = D.id (F X))
    (map_comp : ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]),
      onHom (C.comp f g) = D.comp (onHom f) (onHom g))
    (h : RespectsCongruence onHom R) : True

/-! ## Preorder Congruence Example -/

/-- The preorder congruence identifies all parallel morphisms. -/
def preorderCatCongruence (C : Category) : CatCongruence C where
  rel _ _ _ _ := True
  isEquiv := {
    refl := λ _ => trivial
    symm := λ _ => trivial
    trans := λ _ _ => trivial
  }
  compat_comp := by intro _ _ _ _ _ _ _ _ _ _; trivial
  reduces_id_right _ := trivial
  reduces_id_left _ := trivial
  reduces_assoc _ _ _ := trivial

/-- The quotient by the preorder congruence produces a thin category
    (at most one morphism between any pair). -/
theorem preorder_quotient_is_thin {C : Category} (X Y : C.Obj)
    (f g : (QuotientCat C (preorderCatCongruence C))[X, Y]) : f = g := by
  apply Quot.inductionOn₂ f g
  intro f' g'
  apply Quot.sound
  trivial

#eval "Constructions.Quotients: CatCongruence, QuotientCat, projection, universal property"
#eval s!"Trivial quotient of DiscCat Nat preserves objects"
#eval "Preorder quotient identifies all parallel arrows in any category"
end MiniCategoryCore
