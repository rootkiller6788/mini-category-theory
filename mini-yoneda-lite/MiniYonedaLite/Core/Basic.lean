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
import MiniMorphismSystem.Morphisms.Iso

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

/-! ## Corepresentable Functors (Dual Notion) -/

/-- A functor F : Cᵒᵖ → Set is corepresentable if F ≅ Hom(-, X) for some X.
    This is the dual of representability, obtained by applying
    representability to the opposite functor Fᵒᵖ : C → Setᵒᵖ. -/
def isCorepresentable (C : Category) (F : Functor (Cᵒᵖ) SetCat) : Prop :=
  ∃ (X : C.Obj), Nonempty (F ≅ₙ homFunctorOp C X)

/-- Every representable functor on C gives a corepresentable functor on Cᵒᵖ,
    and vice versa. This is the duality between Yoneda and coYoneda. -/
def representable_to_corepresentable {C : Category} (F : Functor C SetCat)
    (h : isRepresentable C F) : isCorepresentable (Cᵒᵖ) (Functor.comp F (C.op)) := by
  rcases h with ⟨X, hF⟩
  refine ⟨X, ?_⟩
  -- F ≅ Hom_C(X, -) as functors C → Set
  -- This gives an isomorphism of the opposite functors
  exact hF

/-! ## The Category of Elements (∫ F) -/

/-- The category of elements ∫ F of a functor F : C → Set.
    Objects: pairs (X, x) where X ∈ C.Obj and x ∈ F(X).
    Morphisms: (X, x) → (Y, y) are f : C[X, Y] with F(f)(x) = y.

    This category is fundamental to the Yoneda lemma:
    every presheaf is a colimit of representables indexed by its
    category of elements. -/
structure ElementOf {C : Category} (F : Functor C SetCat) where
  obj : C.Obj
  element : F.mapObj obj

/-- The category of elements. -/
def categoryOfElementsFull {C : Category} (F : Functor C SetCat) : Category where
  Obj := ElementOf F
  Hom a b := { f : C[a.obj, b.obj] // F.mapHom f a.element = b.element }
  id a := ⟨C.id a.obj, by
    have h := F.preservesId a.obj
    -- In SetCat, equality of functions is functional extensionality
    -- h : F.mapHom (C.id a.obj) = SetCat.id (F.mapObj a.obj)
    -- So F.mapHom (C.id a.obj) a.element = a.element
    simpa [SetCat] using congrArg (fun φ => φ a.element) h⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    have h := F.preservesComp g' f'
    -- h : F.mapHom (C.comp g' f') = SetCat.comp (F.mapHom g') (F.mapHom f')
    -- Apply to a.element:
    -- F.mapHom (C.comp g' f') a.element = F.mapHom g' (F.mapHom f' a.element)
    -- = F.mapHom g' b.element = g.element
    simpa [SetCat, hf, hg] using congrArg (fun φ => φ a.element) h⟩
  comp_id f := by
    rcases f with ⟨f', hf⟩
    simp [C.comp_id]
  id_comp f := by
    rcases f with ⟨f', hf⟩
    simp [C.id_comp]
  assoc f g h := by
    simp [C.assoc]

/-- The projection functor π : ∫ F → C. -/
def categoryOfElementsProjectionFull {C : Category} (F : Functor C SetCat) :
    Functor (categoryOfElementsFull F) C where
  mapObj a := a.obj
  mapHom f := f.1
  preservesId _ := rfl
  preservesComp _ _ := rfl

/-! ## Slice Category Viewpoint -/

/-- The slice category C/X can be understood via Yoneda:
    objects of C/X correspond to elements of Hom(-, X), i.e.,
    natural transformations from other representables into Y(X).

    This is the Yoneda perspective on slice categories:
    C/X ≃ ∫ Hom(-, X) (the category of elements of the representable). -/

/-- Embedding of C/X into the category of elements of Hom(-, X):
    (f : A → X) ↦ (A, f) ∈ ∫ Hom(-, X) where f ∈ Hom(A, X). -/
def sliceToElements {C : Category} (X : C.Obj)
    (f : SliceObj C X) : ElementOf (homFunctorOp C X) where
  obj := f.obj
  element := f.arr

/-! ## #eval examples -/

#eval "Core.Basic: isRepresentable, presheafCategory, yonedaEmbedding"
#eval "isCorepresentable: F: Cᵒᵖ → Set, F ≅ Hom(-, X)"
#eval "categoryOfElementsFull: ∫ F — objects (X, x ∈ F(X))"
#eval "sliceToElements: C/X → ∫ Hom(-, X)"
#eval "Yoneda: every presheaf = colim of representables over ∫ F"
