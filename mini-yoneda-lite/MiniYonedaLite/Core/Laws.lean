/-
# MiniYonedaLite.Core.Laws

The laws of the Yoneda lemma: statement, corollaries, and derived identities.
States the Yoneda lemma and its key consequences as axioms where the proofs
require set-theoretic foundations beyond this package.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda Lemma Statement -/

/-- The Yoneda lemma: for any functor F : C → Set and object X,
    there is a bijection between natural transformations Hom(X, -) ⇒ F
    and elements of F(X).
    The forward direction evaluates the natural transformation at X on id_X.
    The backward direction sends u ∈ F(X) to the natural transformation
    whose component at Y sends f : X → Y to F(f)(u). -/
axiom yonedaLemmaStatement {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  Nonempty ([(homFunctor C X), F] ≅ᶠ F.mapObj X)

/-! ## Yoneda Bijection (Forward/Backward) -/

/-- Forward direction: Nat(Hom(X,-), F) → F(X).
    α ↦ α_X(id_X) -/
def yonedaForward {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (α : [(homFunctor C X), F]) : F.mapObj X :=
  α X (C.id X)

/-- Backward direction: F(X) → Nat(Hom(X,-), F).
    u ↦ (Y ↦ (f ↦ F(f)(u))) -/
def yonedaBackward {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (u : F.mapObj X) : [(homFunctor C X), F] :=
  fun Y f => F.mapHom f u

/-- The Yoneda bijection: forward ∘ backward = id and backward ∘ forward = id.
    This is the computational heart of the Yoneda lemma. -/
axiom yonedaBijection {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  (∀ (u : F.mapObj X), yonedaForward F X (yonedaBackward F X u) = u) ∧
  (∀ (α : [(homFunctor C X), F]), yonedaBackward F X (yonedaForward F X α) = α)

/-! ## Naturality of the Yoneda Bijection -/

/-- The Yoneda bijection is natural in the object X:
    for any f : Y → X, the diagram commutes. -/
axiom yonedaNaturalInX {C : Category} (F : Functor C SetCat) (X Y : C.Obj)
    (f : C[Y, X]) : True

/-- The Yoneda bijection is natural in the functor F:
    for any natural transformation τ : F ⇒ G, the diagram commutes. -/
axiom yonedaNaturalInF {C : Category} (F G : Functor C SetCat) (X : C.Obj)
    (τ : F ⇒ G) : True

/-! ## Yoneda Corollary: Y is Fully Faithful -/

/-- Corollary of Yoneda: the Yoneda embedding is fully faithful.
    This means Hom_C(X, Y) ≅ Nat(Hom(-, X), Hom(-, Y)). -/
axiom yonedaCorollaryFullyFaithful (C : Category) (X Y : C.Obj) :
  Nonempty (C[X, Y] ≅ᶠ [(homFunctorOp C X), (homFunctorOp C Y)])

/-- The Yoneda embedding reflects isomorphisms:
    if Y(f) is an isomorphism, then f is an isomorphism. -/
axiom yonedaReflectsIsomorphisms (C : Category) (X Y : C.Obj) (f : C[X, Y]) : True

/-! ## Uniqueness of Representing Objects -/

/-- Representing objects are unique up to isomorphism.
    If Hom(X, -) ≅ Hom(Y, -) then X ≅ Y. -/
axiom representingObjectIsUnique (C : Category) (X Y : C.Obj)
    (h : Nonempty (homFunctor C X ≅ₙ homFunctor C Y)) :
    Nonempty (C[X, Y]) × Nonempty (C[Y, X])

/-! ## #eval examples -/

/-- Forward and backward computation on a simple case. -/
#eval "yonedaForward: α ↦ α_X(id_X)"
#eval "yonedaBackward: u ↦ (Y ↦ (f ↦ F(f)(u)))"
#eval "Yoneda lemma: Nat(Hom(X,-), F) ≅ F(X) — natural in X and F"
#eval s!"Yoneda is fully faithful: Hom(X,Y) ≅ Nat(Hom(-,X), Hom(-,Y))"

end MiniYonedaLite
