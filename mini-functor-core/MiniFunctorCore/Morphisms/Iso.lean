/-
# MiniFunctorCore.Morphisms.Iso

Functor isomorphisms in the functor category [C, D].
Natural isomorphisms and their properties.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Natural Isomorphism -/

/--
A natural isomorphism between functors F, G : C → D
is a natural transformation whose components are all isomorphisms.
-/
structure NaturalIsomorphism (C D : Category) (F G : Functor C D) where
  toNatTrans : F ⇒ G
  inverse : G ⇒ F
  leftInv : NatTrans.vcomp inverse toNatTrans = NatTrans.id F
  rightInv : NatTrans.vcomp toNatTrans inverse = NatTrans.id G

notation:60 F:60 " ≅ " G:60 => NaturalIsomorphism _ _ F G

/-! ## Identity Natural Isomorphism -/

def NaturalIsomorphism.id {C D : Category} (F : Functor C D) : F ≅ F where
  toNatTrans := NatTrans.id F
  inverse := NatTrans.id F
  leftInv := by
    funext X; simp [NatTrans.id, NaturalTransformation.vcomp, NatTrans.vcomp]
  rightInv := by
    funext X; simp [NatTrans.id, NaturalTransformation.vcomp, NatTrans.vcomp]

/-! ## Composition of Natural Isomorphisms -/

def NaturalIsomorphism.comp {C D : Category} {F G H : Functor C D}
    (β : G ≅ H) (α : F ≅ G) : F ≅ H where
  toNatTrans := NatTrans.vcomp β.toNatTrans α.toNatTrans
  inverse := NatTrans.vcomp α.inverse β.inverse
  leftInv := by
    calc
      NatTrans.vcomp (NatTrans.vcomp α.inverse β.inverse)
        (NatTrans.vcomp β.toNatTrans α.toNatTrans) =
        NatTrans.vcomp α.inverse
          (NatTrans.vcomp (NatTrans.vcomp β.inverse β.toNatTrans) α.toNatTrans) := by
        funext X; simp [NatTrans.vcomp, NaturalTransformation.vcomp, D.assoc]
      _ = NatTrans.vcomp α.inverse
          (NatTrans.vcomp (NatTrans.id G) α.toNatTrans) := by
        simp [β.leftInv]
      _ = NatTrans.vcomp α.inverse α.toNatTrans := by
        funext X; simp [NatTrans.vcomp, NaturalTransformation.vcomp,
          NatTrans.id, NaturalTransformation.component]
      _ = NatTrans.id F := α.leftInv
  rightInv := by
    calc
      NatTrans.vcomp (NatTrans.vcomp β.toNatTrans α.toNatTrans)
        (NatTrans.vcomp α.inverse β.inverse) =
        NatTrans.vcomp β.toNatTrans
          (NatTrans.vcomp (NatTrans.vcomp α.toNatTrans α.inverse) β.inverse) := by
        funext X; simp [NatTrans.vcomp, NaturalTransformation.vcomp, D.assoc]
      _ = NatTrans.vcomp β.toNatTrans
          (NatTrans.vcomp (NatTrans.id G) β.inverse) := by
        simp [α.rightInv]
      _ = NatTrans.vcomp β.toNatTrans β.inverse := by
        funext X; simp [NatTrans.vcomp, NaturalTransformation.vcomp,
          NatTrans.id, NaturalTransformation.component]
      _ = NatTrans.id H := β.rightInv

/-! ## Inverse of Natural Isomorphism -/

def NaturalIsomorphism.symm {C D : Category} {F G : Functor C D}
    (α : F ≅ G) : G ≅ F where
  toNatTrans := α.inverse
  inverse := α.toNatTrans
  leftInv := α.rightInv
  rightInv := α.leftInv

/-! ## Equivalence of Categories via Functor Category -/

/--
A functor is an equivalence if it induces a natural isomorphism
in the functor category (when restricted appropriately).
-/
structure FunctorEquivalence (C D : Category) where
  F : Functor C D
  G : Functor D C
  unitIso : Functor.comp G F ≅ Functor.id C
  counitIso : Functor.comp F G ≅ Functor.id D

/-! ## Isomorphism in Functor Category -/

/--
An isomorphism in the functor category [C, D] is a natural isomorphism.
-/
def isIsoInFunctorCat {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) : Prop :=
  ∃ (β : G ⇒ F),
    NatTrans.vcomp β α = NatTrans.id F ∧
    NatTrans.vcomp α β = NatTrans.id G

#eval "Morphisms.Iso: NaturalIsomorphism (F ≅ G), id, comp, symm, FunctorEquivalence, isIsoInFunctorCat"
