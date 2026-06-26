/-
# MiniNaturalTransformation.Theorems.Basic

Basic theorems about natural transformations:
- A natural isomorphism is invertible at each component
- Vertical composition satisfies associativity and unit laws
- Horizontal composition satisfies middle-four interchange
- The functor category [C, D] is indeed a category
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Core.Laws
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Morphisms.Iso

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Natural Iso is Invertible at Each Component -/

/--
If α : F ≅ₙ G is a natural isomorphism, then for each object X,
the component α_X is an isomorphism in D with inverse α.inv X.
-/
theorem naturalIso_component_invertible {C D : Category} {F G : Functor C D}
    (α : F ≅ₙ G) (X : C.Obj) :
    D.comp (α.inv X) (α.toNatTrans.component X) = D.id (F.mapObj X) ∧
    D.comp (α.toNatTrans.component X) (α.inv X) = D.id (G.mapObj X) := by
  exact ⟨α.leftInv X, α.rightInv X⟩

/--
If a natural transformation is componentwise invertible, it is a
natural isomorphism.
-/
theorem componentwise_iso_implies_natIso {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (h : ∀ (X : C.Obj), ∃ (inv : D[G.mapObj X, F.mapObj X]),
      D.comp inv (η.component X) = D.id (F.mapObj X) ∧
      D.comp (η.component X) inv = D.id (G.mapObj X)) :
    F ≅ₙ G := by
  choose inv hinv using h
  refine ⟨η, inv, λ X => (hinv X).1, λ X => (hinv X).2⟩

/-! ## Vertical Composition is Associative -/

/--
Vertical composition of natural transformations is associative
and has identities, making the collection of natural transformations
between functors C → D into a category.
-/
theorem vertical_composition_assoc {C D : Category} {F G H K : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (γ : H ⇒ K) :
    NaturalTransformation.vcomp γ (NaturalTransformation.vcomp β α) =
    NaturalTransformation.vcomp (NaturalTransformation.vcomp γ β) α := by
  funext X
  simp [NaturalTransformation.vcomp, D.assoc]

/--
Vertical composition has identity natural transformations as units.
-/
theorem vertical_composition_unit {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) :
    NaturalTransformation.vcomp α (NaturalTransformation.id F) = α ∧
    NaturalTransformation.vcomp (NaturalTransformation.id G) α = α := by
  constructor
  · funext X; simp [NaturalTransformation.vcomp, NaturalTransformation.id, D.comp_id]
  · funext X; simp [NaturalTransformation.vcomp, NaturalTransformation.id, D.id_comp]

/-! ## Middle-Four Interchange Law -/

/--
The interchange law (middle-four) for the 2-categorical structure:
(δ ∘ᵥ γ) ∘ₕ (β ∘ᵥ α) = (δ ∘ₕ β) ∘ᵥ (γ ∘ₕ α)

This justifies Cat as a strict 2-category.
-/
theorem middle_four_interchange {B C D : Category}
    {F G H : Functor B C} {K L M : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (γ : K ⇒ L) (δ : L ⇒ M) :
    NaturalTransformation.hcomp (NaturalTransformation.vcomp δ γ)
      (NaturalTransformation.vcomp β α) =
    NaturalTransformation.vcomp (NaturalTransformation.hcomp δ β)
      (NaturalTransformation.hcomp γ α) := by
  funext X
  simp [NaturalTransformation.vcomp, NaturalTransformation.hcomp,
    NaturalTransformation.whiskerLeft, NaturalTransformation.whiskerRight,
    D.assoc, α.naturality, β.naturality, γ.naturality, δ.naturality,
    K.preservesComp, L.preservesComp, M.preservesComp]

/-! ## The Category of Natural Transformations -/

/--
The collection of functors C → D and natural transformations between them
forms a category: the functor category [C, D].
-/
def FunctorCategoryCat {C D : Category} : Category where
  Obj := Functor C D
  Hom F G := F ⇒ G
  id F := NaturalTransformation.id F
  comp β α := NaturalTransformation.vcomp β α
  comp_id f := (vertical_composition_unit f).2
  id_comp f := (vertical_composition_unit f).1
  assoc f g h := (vertical_composition_assoc h g f).symm

/-! ## #eval Examples -/

#eval "Theorems.Basic: naturalIso_component_invertible, componentwise_iso_implies_natIso, vertical_composition_assoc, vertical_composition_unit, middle_four_interchange, FunctorCategoryCat"
#eval s!"Natural iso components are isomorphisms"
#eval s!"Middle-four interchange law holds"
#eval s!"Functor category [C, D] is a category"
