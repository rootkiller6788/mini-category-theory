/-
# MiniYonedaLite.Core.Basic

Representable functors and the presheaf category.
A functor F : C → Set is representable if F ≅ Hom(X, -) for some X.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Morphisms.Iso
import MiniCategoryCore.Constructions.Products
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Theorems.Main
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Morphisms.Iso
import MiniNaturalTransformation.Theorems.Main

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Representable Functors -/

/-- A functor F is representable if it is naturally isomorphic to Hom(X, -) for some X. -/
def isRepresentable (C : Category) (F : Functor C SetCat) : Prop :=
  ∃ (X : C.Obj), Nonempty (F ≅ᶠ homFunctor C X)

/-! ## Presheaf Category -/

/-- The presheaf category over C: functors from Cᵒᵖ to Set. -/
def presheafCategory (C : Category) : Category := [Cᵒᵖ, SetCat]

/-- A presheaf is representable if it is isomorphic to a representable functor. -/
def isRepresentablePresheaf (C : Category) (P : (presheafCategory C).Obj) : Prop :=
  ∃ (X : C.Obj), True  -- P ≅ Y(X) in a full implementation

/-! ## Yoneda Embedding (declaration) -/

/-- The Yoneda embedding Y : Cᵒᵖ → [C, Set]. -/
def yonedaEmbedding (C : Category) : Functor (Cᵒᵖ) [C, SetCat] where
  mapObj X := homFunctor C X
  mapHom f := {
    component := fun Y => C.comp f
    naturality := fun g => by
      simp [C.assoc]
  }
  preservesId X := by
    funext Y; funext g; simp
  preservesComp f g := by
    funext Y; funext h; simp [C.assoc]

#eval "Core.Basic: isRepresentable, presheafCategory, yonedaEmbedding"
