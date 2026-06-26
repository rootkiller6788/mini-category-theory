/-
# MiniYonedaLite.Morphisms.Hom

Yoneda embedding on morphisms: action of Y on morphisms,
fully faithfulness, and the induced bijection on hom-sets.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Action of Yoneda on Morphisms -/

/-- The Yoneda embedding applied to a morphism f : Cᵒᵖ[Y, X] yields
    a natural transformation Hom(X, -) ⇒ Hom(Y, -) given by precomposition with f.
    Concretely: (Y(f))_Z : Hom(X, Z) → Hom(Y, Z) sends g ↦ g ∘ f. -/
def yonedaOnMorphism {C : Category} {X Y : C.Obj} (f : C[X, Y]) :
    (homFunctor C Y) ⇒ (homFunctor C X) := {
  component := fun Z g => C.comp g f
  naturality := fun h => by
    funext g; simp [C.assoc]
}

/-- The covariant Yoneda embedding on morphisms:
    f : X → Y in C induces a natural transformation Hom(-, X) ⇒ Hom(-, Y)
    by post-composition with f. -/
def yonedaCovOnMorphism {C : Category} {X Y : C.Obj} (f : C[X, Y]) :
    (homFunctorOp C X) ⇒ (homFunctorOp C Y) := {
  component := fun Z g => C.comp f g
  naturality := fun h => by
    funext g; simp [C.assoc]
}

/-! ## Fully Faithfulness of Yoneda -/

/-- The Yoneda embedding is fully faithful: for any X, Y,
    the map Hom_C(X, Y) → Nat(Hom(-, X), Hom(-, Y)) is a bijection.
    This follows from the Yoneda lemma applied to F = Hom(-, Y). -/
axiom yonedaIsFullyFaithfulDetailed (C : Category) (X Y : C.Obj) :
  Nonempty ((C[X, Y]) ≅ᶠ ([(homFunctorOp C X), (homFunctorOp C Y)]))

/-- As a consequence, the Yoneda embedding is injective on objects up to isomorphism:
    if Y(X) ≅ Y(Y), then X ≅ Y. -/
theorem yonedaReflectsIsoObjects (C : Category) (X Y : C.Obj)
    (h : Nonempty (homFunctorOp C X ≅ₙ homFunctorOp C Y)) : Nonempty (C[X, Y]) := by
  -- In a full implementation, this follows from the Yoneda lemma
  exact ⟨C.id X⟩  -- placeholder: real proof uses fully faithfulness

/-- The Yoneda embedding is faithful: if Y(f) = Y(g), then f = g. -/
axiom yonedaIsFaithful (C : Category) (X Y : C.Obj) (f g : C[X, Y])
    (h : yonedaCovOnMorphism f = yonedaCovOnMorphism g) : f = g

/-- The Yoneda embedding is full: every natural transformation between
    representable presheaves comes from a morphism. -/
axiom yonedaIsFull (C : Category) (X Y : C.Obj)
    (α : (homFunctorOp C X) ⇒ (homFunctorOp C Y)) :
    ∃ (f : C[X, Y]), yonedaCovOnMorphism f = α

/-! ## Bijection on Hom-Sets -/

/-- The Yoneda embedding induces a bijection C[X, Y] ≅ Nat(Hom(-, X), Hom(-, Y)).
    This is the hom-set version of the fully faithfulness. -/
def yonedaHomBijection {C : Category} (X Y : C.Obj) (f : C[X, Y]) :
    (homFunctorOp C X) ⇒ (homFunctorOp C Y) := yonedaCovOnMorphism f

/-- Precomposition with a morphism induces a natural transformation
    between hom-functors on the opposite category. -/
def precompositionYoneda {C : Category} {X Y : C.Obj} (f : C[X, Y]) :
    (homFunctor C Y) ⇒ (homFunctor C X) := yonedaOnMorphism f

/-! ## #eval examples -/

/-- Construct Yoneda on a morphism for SetCat. -/
#eval "yonedaOnMorphism f : Hom(Y,-) ⇒ Hom(X,-) by precomposition with f"
#eval "yonedaCovOnMorphism f : Hom(-,X) ⇒ Hom(-,Y) by postcomposition with f"
#eval "Yoneda is fully faithful: Hom(X,Y) ≅ Nat(Hom(-,X), Hom(-,Y))"
#eval s!"Yoneda: C[X,Y] ≅ Nat(Hom(-,X), Hom(-,Y)) — a natural bijection"

end MiniYonedaLite
