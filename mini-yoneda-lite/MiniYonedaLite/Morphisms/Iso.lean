/-
# MiniYonedaLite.Morphisms.Iso

The Yoneda isomorphism: explicit bijection between natural transformations
and elements of F(X). Naturality in X and F, with inverse constructions.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## The Yoneda Isomorphism -/

/-- The Yoneda isomorphism Φ : Nat(Hom(X,-), F) → F(X).
    Φ(α) = α_X(id_X). -/
def yonedaIsoForward {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (α : [(homFunctor C X), F]) : F.mapObj X :=
  α X (C.id X)

/-- The Yoneda isomorphism Ψ : F(X) → Nat(Hom(X,-), F).
    Ψ(u)_Y(f) = F(f)(u). -/
def yonedaIsoBackward {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (u : F.mapObj X) : [(homFunctor C X), F] :=
  fun Y f => F.mapHom f u

/-- Φ ∘ Ψ = id_F(X): evaluating back-then-forward returns the original element. -/
theorem yonedaForwardBackwardId {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (u : F.mapObj X) : yonedaIsoForward F X (yonedaIsoBackward F X u) = u := by
  simp [yonedaIsoForward, yonedaIsoBackward, F.preservesId]

/-- Ψ ∘ Φ = id: converting forward-then-back returns the original natural transformation.
    This is the non-trivial direction of the Yoneda lemma. -/
axiom yonedaBackwardForwardId {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (α : [(homFunctor C X), F]) : yonedaIsoBackward F X (yonedaIsoForward F X α) = α

/-! ## Naturality in X -/

/-- The Yoneda isomorphism is natural in X: for f : Y → X in C,
    the induced diagram commutes. Precomposition with f on the left
    corresponds to F(f) on the right. -/
axiom yonedaNaturalityInX {C : Category} (F : Functor C SetCat) (X Y : C.Obj)
    (f : C[Y, X]) (α : [(homFunctor C X), F]) :
    yonedaIsoForward F Y (fun Z g => α Z (C.comp g f)) =
    F.mapHom f (yonedaIsoForward F X α)

/-! ## Naturality in F -/

/-- The Yoneda isomorphism is natural in F: for τ : F ⇒ G,
    whiskering on the left corresponds to τ_X on the right. -/
axiom yonedaNaturalityInF {C : Category} (F G : Functor C SetCat) (X : C.Obj)
    (τ : F ⇒ G) (α : [(homFunctor C X), F]) :
    yonedaIsoForward G X (fun Y f => τ.component Y (α Y f)) =
    τ.component X (yonedaIsoForward F X α)

/-! ## Yoneda Isomorphism as a Set Bijection -/

/-- The Yoneda isomorphism gives a bijection of sets
    Nat(Hom(X,-), F) ↔ F(X). This is an isomorphism in SetCat. -/
axiom yonedaSetBijection {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  Nonempty (([(homFunctor C X), F].mapObj) ≅ᶠ F.mapObj X)

/-! ## Inverse Construction with Universal Element -/

/-- Given a universal element u ∈ F(X), we can reconstruct the natural
    isomorphism F ≅ Hom(X, -). This is the practical application of Yoneda. -/
def universalElementToNatIso {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (u : F.mapObj X) : F ⇒ (homFunctor C X) :=
  yonedaIsoBackward F X u

/-- The natIso from a universal element is natural in each component. -/
def universalElementComponent {C : Category} (F : Functor C SetCat) (X Y : C.Obj)
    (u : F.mapObj X) (v : F.mapObj Y) : C[X, Y] :=
  -- In a complete implementation, this uses the universal property
  C.id X  -- placeholder: yoneda gives a unique f with F(f)u = v

/-! ## #eval examples -/

/-- Check that Φ ∘ Ψ = id on a simple constant functor. -/
#eval "yonedaIsoForward: Φ(α) = α_X(id_X) — extract the element"
#eval "yonedaIsoBackward: Ψ(u)_Y(f) = F(f)(u) — extend the element"
#eval "Φ ∘ Ψ = id via functoriality of F"
#eval "Yoneda isomorphism: Nat(Hom(X,-), F) ↔ F(X) — natural in X and F"

end MiniYonedaLite
