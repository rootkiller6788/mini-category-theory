/-
# MiniNaturalTransformation.Morphisms.Iso

Natural isomorphisms: natural transformations where every component
is an isomorphism in the target category. Includes construction,
composition, symmetry, and tests.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Core.Laws

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Natural Isomorphism -/

/--
A natural isomorphism between functors F, G : C → D consists of:
- A natural transformation η : F ⇒ G
- For each X, an inverse morphism η_X^{-1} : G(X) → F(X)
- Left and right inverse laws componentwise
-/
structure NaturalIsomorphism {C D : Category} (F G : Functor C D) where
  toNatTrans : F ⇒ G
  inv : ∀ (X : C.Obj), D[G.mapObj X, F.mapObj X]
  leftInv : ∀ (X : C.Obj), D.comp (inv X) (toNatTrans.component X) = D.id (F.mapObj X)
  rightInv : ∀ (X : C.Obj), D.comp (toNatTrans.component X) (inv X) = D.id (G.mapObj X)

notation:50 F:50 " ≅ₙ " G:50 => NaturalIsomorphism F G

/-! ## Predicate: isNaturalIso -/

/--
A natural transformation α : F ⇒ G is a natural isomorphism if each
component α_X is an isomorphism in D.
-/
def isNaturalIso {C D : Category} {F G : Functor C D} (α : F ⇒ G) : Prop :=
  ∀ (X : C.Obj), ∃ (inv : D[G.mapObj X, F.mapObj X]),
    D.comp inv (α.component X) = D.id (F.mapObj X) ∧
    D.comp (α.component X) inv = D.id (G.mapObj X)

/-! ## Identity Natural Isomorphism -/

/--
The identity natural isomorphism id_F : F ≅ₙ F.
-/
def NaturalIsomorphism.id {C D : Category} (F : Functor C D) : F ≅ₙ F where
  toNatTrans := NaturalTransformation.id F
  inv X := D.id (F.mapObj X)
  leftInv X := by simp
  rightInv X := by simp

/-! ## Composition of Natural Isomorphisms -/

/--
Vertical composition of natural isomorphisms: β ∘ₙ α where α : F ≅ₙ G, β : G ≅ₙ H.
-/
def NaturalIsomorphism.comp {C D : Category} {F G H : Functor C D}
    (β : G ≅ₙ H) (α : F ≅ₙ G) : F ≅ₙ H where
  toNatTrans := NaturalTransformation.vcomp β.toNatTrans α.toNatTrans
  inv X := D.comp (α.inv X) (β.inv X)
  leftInv X := by
    calc
      D.comp (D.comp (α.inv X) (β.inv X))
        (D.comp (β.toNatTrans.component X) (α.toNatTrans.component X)) =
        D.comp (α.inv X) (D.comp (D.comp (β.inv X) (β.toNatTrans.component X))
          (α.toNatTrans.component X)) := by
        simp [D.assoc]
      _ = D.comp (α.inv X) (D.comp (D.id (G.mapObj X)) (α.toNatTrans.component X)) := by
        rw [β.leftInv]
      _ = D.comp (α.inv X) (α.toNatTrans.component X) := by simp
      _ = D.id (F.mapObj X) := α.leftInv X
  rightInv X := by
    calc
      D.comp (D.comp (β.toNatTrans.component X) (α.toNatTrans.component X))
        (D.comp (α.inv X) (β.inv X)) =
        D.comp (β.toNatTrans.component X) (D.comp (D.comp (α.toNatTrans.component X)
          (α.inv X)) (β.inv X)) := by
        simp [D.assoc]
      _ = D.comp (β.toNatTrans.component X) (D.comp (D.id (G.mapObj X)) (β.inv X)) := by
        rw [α.rightInv]
      _ = D.comp (β.toNatTrans.component X) (β.inv X) := by simp
      _ = D.id (H.mapObj X) := β.rightInv X

/-! ## Inverse (Symmetry) of Natural Isomorphism -/

/--
The inverse of a natural isomorphism α : F ≅ₙ G is β : G ≅ₙ F.
The key insight: the componentwise inverses automatically form
a natural transformation.
-/
def NaturalIsomorphism.symm {C D : Category} {F G : Functor C D}
    (α : F ≅ₙ G) : G ≅ₙ F where
  toNatTrans := {
    component X := α.inv X
    naturality {X Y} f := by
      have h := α.toNatTrans.naturality f
      calc
        D.comp (α.inv Y) (G.mapHom f) =
          D.comp (D.comp (α.inv Y) (G.mapHom f))
            (D.comp (α.toNatTrans.component X) (α.inv X)) := by
          rw [α.rightInv X, D.comp_id]
        _ = D.comp (D.comp (D.comp (α.inv Y) (G.mapHom f))
            (α.toNatTrans.component X)) (α.inv X) := by
          simp [D.assoc]
        _ = D.comp (D.comp (α.inv Y) (D.comp (G.mapHom f)
            (α.toNatTrans.component X))) (α.inv X) := by
          simp [D.assoc]
        _ = D.comp (D.comp (α.inv Y) (D.comp (α.toNatTrans.component Y)
            (F.mapHom f))) (α.inv X) := by
          rw [← h]
        _ = D.comp (D.comp (D.comp (α.inv Y) (α.toNatTrans.component Y))
            (F.mapHom f)) (α.inv X) := by
          simp [D.assoc]
        _ = D.comp (D.comp (D.id (F.mapObj Y)) (F.mapHom f)) (α.inv X) := by
          rw [α.leftInv Y]
        _ = D.comp (F.mapHom f) (α.inv X) := by simp
  }
  inv X := α.toNatTrans.component X
  leftInv X := α.rightInv X
  rightInv X := α.leftInv X

/-! ## Construction from Components -/

/--
Construct a natural isomorphism from component data and proof that
each component is an isomorphism.
-/
def mkNatIsoFromComponents {C D : Category} {F G : Functor C D}
    (comp : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X])
    (comp_natural : ∀ {X Y : C.Obj} (f : C[X, Y]),
      D.comp (comp Y) (F.mapHom f) = D.comp (G.mapHom f) (comp X))
    (inv : ∀ (X : C.Obj), D[G.mapObj X, F.mapObj X])
    (left_inv : ∀ (X : C.Obj), D.comp (inv X) (comp X) = D.id (F.mapObj X))
    (right_inv : ∀ (X : C.Obj), D.comp (comp X) (inv X) = D.id (G.mapObj X)) :
    F ≅ₙ G :=
  ⟨{ component := comp, naturality := comp_natural }, inv, left_inv, right_inv⟩

/-! ## #eval Examples -/

/-- Identity natural isomorphism on listFunctor. -/
def idNtIso : listFunctor ≅ₙ listFunctor := NaturalIsomorphism.id listFunctor

/-- The reverse natural isomorphism on lists: reverse is a natural isomorphism. -/
def reverseNatIso : listFunctor ≅ₙ listFunctor :=
  mkNatIsoFromComponents
    (λ X xs => xs.reverse)
    (by
      intro X Y f
      funext xs
      simp [List.map_reverse])
    (λ X xs => xs.reverse)
    (by intro X; funext xs; simp [List.reverse_reverse])
    (by intro X; funext xs; simp [List.reverse_reverse])

/-- The symmetric of reverse is itself. -/
def reverseNatSymm : listFunctor ≅ₙ listFunctor := reverseNatIso.symm

#eval "Morphisms.Iso: NaturalIsomorphism (≅ₙ), isNaturalIso, id, comp, symm, mkNatIsoFromComponents"
#eval s!"Identity: listFunctor ≅ₙ listFunctor"
#eval reverseNatIso.toNatTrans.component Nat ([1,2,3] : List Nat)
#eval reverseNatSymm.toNatTrans.component Nat ([3,2,1] : List Nat)
