/-
# MiniMorphismSystem.Morphisms.Iso

Functor isomorphisms (natural isomorphisms) and equivalence of categories.
An equivalence consists of functors forth/back with unit and counit
natural isomorphisms satisfying the triangle identities.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Functor Isomorphism (Natural Isomorphism) -/

/--
A natural isomorphism between functors F, G : C → D.
For each object X, a morphism component X : F(X) → G(X) that is iso,
with an inverse inv X : G(X) → F(X) giving two-sided identity.
-/
structure FunctorIso {C D : Category} (F G : Functor C D) where
  component : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]
  inv : ∀ (X : C.Obj), D[G.mapObj X, F.mapObj X]
  leftInv : ∀ (X : C.Obj), D.comp (inv X) (component X) = D.id (F.mapObj X)
  rightInv : ∀ (X : C.Obj), D.comp (component X) (inv X) = D.id (G.mapObj X)
  naturality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (F.mapHom f) = D.comp (G.mapHom f) (component X)

notation:50 F:50 " ≅ᶠ " G:50 => FunctorIso F G

/-- Identity functor isomorphism. -/
def FunctorIso.id {C D : Category} (F : Functor C D) : F ≅ᶠ F where
  component X := D.id (F.mapObj X)
  inv X := D.id (F.mapObj X)
  leftInv X := D.comp_id (D.id (F.mapObj X))
  rightInv X := D.comp_id (D.id (F.mapObj X))
  naturality f := by
    simp [D.id_comp, D.comp_id]

/-- Inverse (symmetry) of a functor isomorphism. -/
def FunctorIso.symm {C D : Category} {F G : Functor C D} (α : F ≅ᶠ G) : G ≅ᶠ F where
  component X := α.inv X
  inv X := α.component X
  leftInv X := α.rightInv X
  rightInv X := α.leftInv X
  naturality {X Y} f := by
    -- From α.naturality: comp(α_Y, Ff) = comp(Gf, α_X)
    -- We need: comp(α⁻¹_Y, Gf) = comp(Ff, α⁻¹_X)
    -- This follows by applying α⁻¹ to both sides of α.naturality
    -- which gives: α⁻¹_Y ∘ Gf ∘ α_X = Ff
    -- Then α⁻¹_Y ∘ Gf = Ff ∘ α⁻¹_X
    -- The formal proof uses the inverse properties
    calc
      D.comp (α.inv Y) (G.mapHom f)
          = D.comp (α.inv Y) (D.comp (G.mapHom f) (D.id (G.mapObj X))) := by rw [D.comp_id]
      _ = D.comp (α.inv Y) (D.comp (G.mapHom f)
            (D.comp (α.component X) (α.inv X))) := by rw [α.rightInv X, D.id_comp]
      _ = D.comp (α.inv Y) (D.comp (D.comp (G.mapHom f) (α.component X)) (α.inv X)) := by
        rw [D.assoc]
      _ = D.comp (α.inv Y) (D.comp (D.comp (α.component Y) (F.mapHom f)) (α.inv X)) := by
        rw [α.naturality f]
      _ = D.comp (α.inv Y) (D.comp (α.component Y) (D.comp (F.mapHom f) (α.inv X))) := by
        rw [D.assoc (α.component Y) (F.mapHom f) (α.inv X)]
      _ = D.comp (D.comp (α.inv Y) (α.component Y)) (D.comp (F.mapHom f) (α.inv X)) := by
        rw [D.assoc]
      _ = D.comp (D.id (F.mapObj Y)) (D.comp (F.mapHom f) (α.inv X)) := by rw [α.leftInv Y]
      _ = D.comp (F.mapHom f) (α.inv X) := by rw [D.id_comp]

/-- Vertical composition of functor isomorphisms: α : F ≅ G, β : G ≅ H → β ∘ α : F ≅ H. -/
def FunctorIso.vcomp {C D : Category} {F G H : Functor C D} (α : F ≅ᶠ G) (β : G ≅ᶠ H) : F ≅ᶠ H where
  component X := D.comp (β.component X) (α.component X)
  inv X := D.comp (α.inv X) (β.inv X)
  leftInv X := by
    calc
      D.comp (D.comp (α.inv X) (β.inv X)) (D.comp (β.component X) (α.component X))
          = D.comp (α.inv X) (D.comp (β.inv X) (D.comp (β.component X) (α.component X))) := by
        rw [D.assoc]
      _ = D.comp (α.inv X) (D.comp (D.comp (β.inv X) (β.component X)) (α.component X)) := by
        rw [D.assoc (β.inv X) (β.component X) (α.component X)]
      _ = D.comp (α.inv X) (D.comp (D.id (G.mapObj X)) (α.component X)) := by rw [β.leftInv X]
      _ = D.comp (α.inv X) (α.component X) := by rw [D.id_comp]
      _ = D.id (F.mapObj X) := α.leftInv X
  rightInv X := by
    calc
      D.comp (D.comp (β.component X) (α.component X)) (D.comp (α.inv X) (β.inv X))
          = D.comp (β.component X) (D.comp (α.component X) (D.comp (α.inv X) (β.inv X))) := by
        rw [D.assoc]
      _ = D.comp (β.component X) (D.comp (D.comp (α.component X) (α.inv X)) (β.inv X)) := by
        rw [D.assoc (α.component X) (α.inv X) (β.inv X)]
      _ = D.comp (β.component X) (D.comp (D.id (G.mapObj X)) (β.inv X)) := by rw [α.rightInv X]
      _ = D.comp (β.component X) (β.inv X) := by rw [D.id_comp]
      _ = D.id (H.mapObj X) := β.rightInv X
  naturality f := by
    calc
      D.comp (D.comp (β.component Y) (α.component Y)) (F.mapHom f)
          = D.comp (β.component Y) (D.comp (α.component Y) (F.mapHom f)) := by rw [D.assoc]
      _ = D.comp (β.component Y) (D.comp (G.mapHom f) (α.component X)) := by rw [α.naturality f]
      _ = D.comp (D.comp (β.component Y) (G.mapHom f)) (α.component X) := by rw [D.assoc]
      _ = D.comp (D.comp (H.mapHom f) (β.component X)) (α.component X) := by rw [β.naturality f]
      _ = D.comp (H.mapHom f) (D.comp (β.component X) (α.component X)) := by rw [← D.assoc]

/-! ## Equivalence of Categories -/

/--
An equivalence of categories C and D consists of:
- A functor forth : C → D
- A functor back  : D → C
- A natural isomorphism unit : id_C ≅ back ∘ forth
- A natural isomorphism counit : forth ∘ back ≅ id_D
- Triangle identities ensuring coherence
-/
structure Equivalence (C D : Category) where
  forth : Functor C D
  back  : Functor D C
  unitIso  : Functor.id C ≅ᶠ Functor.comp back forth
  counitIso : Functor.comp forth back ≅ᶠ Functor.id D
  -- Triangle identity 1: (counit ∘ forth) • (forth ∘ unit) = id_forth
  -- That is: for each X, comp(counit_{F X}, F(unit_X)) = id_{F X}
  triangle1 : ∀ (X : C.Obj),
    D.comp (counitIso.component (forth.mapObj X)) (forth.mapHom (unitIso.component X)) = D.id (forth.mapObj X)
  -- Triangle identity 2: (back ∘ counit) • (unit ∘ back) = id_back
  -- That is: for each Y, comp(G(counit_Y), unit_{G Y}) = id_{G Y}
  triangle2 : ∀ (Y : D.Obj),
    C.comp (back.mapHom (counitIso.component Y)) (unitIso.component (back.mapObj Y)) = C.id (back.mapObj Y)

/--
A functor F is part of an equivalence iff there exists G and unit/counit
satisfying the axioms. We also say F is an equivalence of categories.
-/
def IsEquivalence {C D : Category} (F : Functor C D) : Prop :=
  ∃ (e : Equivalence C D), e.forth = F

#eval "Morphisms.Iso: FunctorIso with naturality, Equivalence with triangle identities"
#eval "fwd/inv/leftInv/rightInv/naturality; vcomp, symm, id for FunctorIso"
end MiniMorphismSystem
