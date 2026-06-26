/-
# MiniNaturalTransformation.Theorems.Classification

Classification of natural transformations by component, and the result
that a fully faithful functor reflects natural isomorphisms.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Hom
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Iso

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Classification by Component -/

/--
Two natural transformations α, β : F ⇒ G are equal iff they have
equal components at every object X.
-/
theorem classification_by_component {C D : Category} {F G : Functor C D}
    (α β : F ⇒ G) : α = β ↔ ∀ (X : C.Obj), α.component X = β.component X := by
  constructor
  · intro h X; rw [h]
  · intro h
    cases α; cases β
    simp at h
    simp [h]

/--
A natural transformation is determined by its component functions.
-/
theorem natTrans_determined_by_components {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) : α = { component := α.component
      naturality := α.naturality } := rfl

/-! ## Fully Faithful Functors Reflect Natural Isomorphisms -/

/--
If H : D → E is fully faithful, then a natural transformation
α : F ⇒ G is a natural isomorphism iff H(α) : H∘F ⇒ H∘G is a
natural isomorphism.
-/
theorem fullyFaithful_reflects_natIso {C D E : Category}
    (H : Functor D E) (hFF : H.IsFullyFaithful)
    {F G : Functor C D} (α : F ⇒ G)
    (h : isNaturalIso { component := λ X => H.mapHom (α.component X)
      naturality := λ f => by
        simp [← H.preservesComp, α.naturality f] }) :
    isNaturalIso α := by
  intro X
  rcases h X with ⟨inv, linv, rinv⟩
  rcases hFF.1 inv with ⟨inv', hinv'⟩
  refine ⟨inv', ?_, ?_⟩
  · apply hFF.2
    calc
      H.mapHom (D.comp inv' (α.component X)) =
        E.comp (H.mapHom inv') (H.mapHom (α.component X)) := H.preservesComp _ _
      _ = E.comp inv (H.mapHom (α.component X)) := by rw [hinv']
      _ = E.id (H.mapObj (F.mapObj X)) := linv
      _ = H.mapHom (D.id (F.mapObj X)) := by rw [H.preservesId]
  · apply hFF.2
    calc
      H.mapHom (D.comp (α.component X) inv') =
        E.comp (H.mapHom (α.component X)) (H.mapHom inv') := H.preservesComp _ _
      _ = E.comp (H.mapHom (α.component X)) inv := by rw [hinv']
      _ = E.id (H.mapObj (G.mapObj X)) := rinv
      _ = H.mapHom (D.id (G.mapObj X)) := by rw [H.preservesId]

/-! ## Classification by Target Category -/

/--
For SetCat-valued functors, natural transformations are determined by
their action on elements.
-/
structure SetNatData (F G : Functor SetCat SetCat) where
  map_elt : ∀ (X : Type) (x : F.mapObj X), G.mapObj X
  natural : ∀ (X Y : Type) (f : X → Y) (x : F.mapObj X),
    map_elt Y (F.mapHom f x) = G.mapHom f (map_elt X x)

/--
Convert set-theoretic natural data to a natural transformation.
-/
def setNatData_to_NatTrans {F G : Functor SetCat SetCat}
    (d : SetNatData F G) : F ⇒ G where
  component X := d.map_elt X
  naturality {X Y} f := by
    funext x
    apply d.natural X Y f x

/--
Convert a natural transformation to set-theoretic natural data.
-/
def natTrans_to_setNatData {F G : Functor SetCat SetCat}
    (η : F ⇒ G) : SetNatData F G where
  map_elt X x := η.component X x
  natural X Y f x := by
    have h := congrFun (η.naturality f) x
    simp at h
    exact h

/-! ## #eval Examples -/

/-- Identity natural transformation data. -/
def idSetNatData : SetNatData listFunctor listFunctor :=
  natTrans_to_setNatData (NaturalTransformation.id listFunctor)

#eval "Theorems.Classification: classification_by_component, fullyFaithful_reflects_natIso, SetNatData, setNatData_to_NatTrans, natTrans_to_setNatData"
#eval s!"Natural transformations classified by components"
#eval s!"Fully faithful functors reflect natural isomorphisms"
#eval s!"SetNatData: element-level description of natural transformations"
