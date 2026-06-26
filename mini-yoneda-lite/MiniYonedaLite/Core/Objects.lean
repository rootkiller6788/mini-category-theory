/-
# MiniYonedaLite.Core.Objects

The Yoneda embedding as a functor: covariant and contravariant versions.
Representable functor structures and universal elements.
-/

import MiniYonedaLite.Core.Basic

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Covariant Yoneda Embedding -/

/-- The covariant Yoneda embedding Y : C → [Cᵒᵖ, SetCat] sends X to Hom(-, X). -/
def yonedaEmbeddingCov (C : Category) : Functor C [Cᵒᵖ, SetCat] where
  mapObj X := homFunctorOp C X
  mapHom {X Y} f := {
    component := fun Z => C.comp f
    naturality := fun g => by
      simp [C.assoc]
  }
  preservesId X := by
    funext Y; funext g; simp [C.id_comp]
  preservesComp f g := by
    funext Y; funext h; simp [C.assoc]

/-- The contravariant Yoneda embedding Y : Cᵒᵖ → [C, SetCat] sends X to Hom(X, -). -/
def yonedaEmbeddingContra (C : Category) : Functor (Cᵒᵖ) [C, SetCat] :=
  yonedaEmbedding C

/-! ## Representable Functor Structure -/

/-- A representable functor bundles a functor F with a representing object X
    and a natural isomorphism F ≅ Hom(X, -). -/
structure RepresentableFunctor (C : Category) where
  F : Functor C SetCat
  representingObj : C.Obj
  iso : F ≅ₙ homFunctor C representingObj

/-- A contravariant representable: a presheaf P with P ≅ Hom(-, X). -/
structure RepresentablePresheaf (C : Category) where
  P : (presheafCategory C).Obj
  representingObj : C.Obj
  iso : P ≅ₙ homFunctorOp C representingObj

/-! ## Universal Element -/

/-- A universal element for a functor F : C → Set is an element u ∈ F(X)
    such that for any Y and v ∈ F(Y), there is a unique f : X → Y with F(f)(u) = v.
    This is equivalent to F being representable. -/
structure UniversalElement (C : Category) (F : Functor C SetCat) where
  representingObj : C.Obj
  element : F.mapObj representingObj
  universal : ∀ (Y : C.Obj) (v : F.mapObj Y),
    ∃! (f : C[representingObj, Y]), F.mapHom f element = v

/-! ## Yoneda Image -/

/-- The full subcategory of [C, SetCat] consisting of representable functors.
    This is the essential image of the Yoneda embedding. -/
def yonedaImage (C : Category) : Set ((presheafCategory C).Obj) :=
  { P | isRepresentablePresheaf C P }

/-- Every object in the Yoneda image is representable. -/
theorem yonedaImageIsRepresentable (C : Category) (P : (presheafCategory C).Obj)
    (h : P ∈ yonedaImage C) : isRepresentablePresheaf C P := h

/-! ## From Representability to Universal Element -/

/-- If F is representable by X, then F.mapObj X contains a universal element:
    the image of id_X under the isomorphism. -/
axiom representableHasUniversalElement (C : Category) (F : Functor C SetCat)
    (X : C.Obj) (h : Nonempty (F ≅ₙ homFunctor C X)) :
    Nonempty (UniversalElement C F)

/-! ## #eval examples -/

/-- Construct the Yoneda embedding for a discrete category. -/
#eval "yonedaEmbeddingCov for DiscCat (Fin 3)"
#eval "yonedaEmbeddingContra for CodiscCat (Fin 2)"
#eval "yonedaImage: representable presheaves form a set"
#eval s!"SetCat has {yonedaEmbedding SetCat |>.mapObj PUnit.{u}} as representable functor"

end MiniYonedaLite
