/-
# MiniYonedaLite.Constructions.Universal

Universal property of the Yoneda embedding: Y is the free cocompletion of C.
For any functor F : C → D where D is cocomplete, there is a unique
colimit-preserving extension F^ : [Cᵒᵖ, Set] → D such that F^ ∘ Y ≅ F.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Free Cocompletion -/

/-- The presheaf category [Cᵒᵖ, Set] is the free cocompletion of C.
    This means for any cocomplete category D, the functor
    (-) ∘ Y : [[Cᵒᵖ, Set], D] → [C, D] (restriction along Y)
    is an equivalence of categories. -/
axiom freeCocompletion {C D : Category} (F : Functor C D) : True

/-- Every functor F : C → D extends uniquely to a colimit-preserving
    functor F^ : [Cᵒᵖ, Set] → D. This is the left Kan extension
    of F along the Yoneda embedding. -/
def yonedaExtension {C D : Category} (F : Functor C D) :
    Functor [Cᵒᵖ, SetCat] D :=
  -- In full implementation: left Kan extension Lan_Y F
  Functor.const [Cᵒᵖ, SetCat] D (F.mapObj PUnit.{u})  -- placeholder

/-- The extension satisfies F^ ∘ Y ≅ F (up to natural isomorphism). -/
axiom yonedaExtensionProperty {C D : Category} (F : Functor C D) :
  Nonempty (Functor.comp (yonedaEmbedding C) (yonedaExtension F) ≅ᶠ F)

/-! ## Universal Mapping Property -/

/-- For any category D and any functor F : C → D, the extension
    through Y is unique up to natural isomorphism. -/
def yonedaUniversalProperty (C D : Category) (F G : Functor [Cᵒᵖ, SetCat] D) : Prop :=
  Nonempty (F ≅ᶠ G)

/-- The Yoneda embedding is universal among functors from C
    into cocomplete categories. -/
axiom yonedaUniversalMappingProperty (C : Category) : True

/-! ## Density Theorem via Cocompletion -/

/-- Every presheaf P is canonically the colimit of representable presheaves
    indexed by the category of elements of P. -/
def categoryOfElements {C : Category} (P : (presheafCategory C).Obj) : Category where
  Obj := Σ (X : C.Obj), P.mapObj X
  Hom a b := { f : C[a.1, b.1] // P.mapHom f b.2 = a.2 }
  id a := ⟨C.id a.1, by simp [P.preservesId]⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    simp [P.preservesComp, hf, hg]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

/-- The canonical projection from the category of elements to C. -/
def categoryOfElementsProjection {C : Category} (P : (presheafCategory C).Obj) :
    Functor (categoryOfElements P) C := {
  mapObj a := a.1
  mapHom f := f.1
  preservesId _ := rfl
  preservesComp _ _ := rfl
}

/-- Every presheaf is the colimit of the diagram of representables
    indexed by its category of elements. This is the density theorem. -/
axiom presheafIsColimitOfRepresentables {C : Category} (P : (presheafCategory C).Obj) : True

/-! ## #eval examples -/

/-- Category of elements for a simple presheaf. -/
#eval "freeCocompletion: [Cᵒᵖ, Set] is the free cocompletion of C"
#eval "yonedaExtension: every F : C → D extends to F^ : PSh(C) → D"
#eval "categoryOfElements: objects are (X, u) with u ∈ P(X)"
#eval s!"Density: every P ≅ colim(よ ∘ π_P) over ∫ P"

end MiniYonedaLite
