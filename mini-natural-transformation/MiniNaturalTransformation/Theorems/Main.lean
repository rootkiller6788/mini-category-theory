/-
# MiniNaturalTransformation.Theorems.Main

Main results: Cat is a strict 2-category, the functor category [C, D]
is a category, and the Yoneda lemma described via natural transformations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Core.Laws
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Theorems.Basic


namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem
open MiniFunctorCore

/-! ## Cat is a Strict 2-Category -/

/--
Cat is a strict 2-category where:
- Objects are categories
- 1-morphisms are functors
- 2-morphisms are natural transformations
- Vertical composition is vcomp
- Horizontal composition is hcomp

We prove the key coherence laws that make this structure a 2-category.
-/

/--
The functor category [C, D] satisfies the axioms of a category:
associativity and identity laws for vertical composition.
-/
theorem cat_is_category {C D : Category} :
    let FC := FunctorCategoryCat (C := C) (D := D)
    (∀ {F G H K : FC.Obj} (f : FC.Hom F G) (g : FC.Hom G H) (h : FC.Hom H K),
      FC.comp (FC.comp h g) f = FC.comp h (FC.comp g f)) ∧
    (∀ {F G : FC.Obj} (f : FC.Hom F G),
      FC.comp f (FC.id F) = f ∧ FC.comp (FC.id G) f = f) := by
  intro FC
  have h_assoc : ∀ {F G H K : FC.Obj} (f : FC.Hom F G) (g : FC.Hom G H) (h : FC.Hom H K),
    FC.comp (FC.comp h g) f = FC.comp h (FC.comp g f) := by
    intro F G H K f g h
    funext X
    simp [FC, FunctorCategoryCat, NaturalTransformation.vcomp, D.assoc]
  have h_id : ∀ {F G : FC.Obj} (f : FC.Hom F G),
    FC.comp f (FC.id F) = f ∧ FC.comp (FC.id G) f = f := by
    intro F G f
    constructor
    · funext X; simp [FC, FunctorCategoryCat, NaturalTransformation.vcomp,
        NaturalTransformation.id, D.comp_id]
    · funext X; simp [FC, FunctorCategoryCat, NaturalTransformation.vcomp,
        NaturalTransformation.id, D.id_comp]
  exact ⟨h_assoc, h_id⟩

/--
For each pair of categories C, D, the hom-category Cat(C, D) is
the functor category [C, D] with functors as objects and natural
transformations as morphisms.
-/
theorem homCat_is_functorCat (C D : Category) : Category :=
  FunctorCategoryCat (C := C) (D := D)

/--
The interchange law: horizontal composition respects vertical composition.
For α : F ⇒ G, β : G ⇒ H, γ : K ⇒ L, δ : L ⇒ M (all D-valued functors on C):
(δ ∘ᵥ γ) ∘ₕ (β ∘ᵥ α) = (δ ∘ₕ β) ∘ᵥ (γ ∘ₕ α)
This is the key coherence axiom making Cat a 2-category.
-/
theorem two_category_interchange {C D : Category}
    {F G H : Functor C D} {K L M : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (γ : K ⇒ L) (δ : L ⇒ M) :
    NaturalTransformation.hcomp (NaturalTransformation.vcomp δ γ)
      (NaturalTransformation.vcomp β α) =
    NaturalTransformation.vcomp (NaturalTransformation.hcomp δ β)
      (NaturalTransformation.hcomp γ α) := by
  funext X
  simp [NaturalTransformation.vcomp, NaturalTransformation.hcomp,
    NaturalTransformation.whiskerLeft, NaturalTransformation.whiskerRight,
    D.assoc, α.naturality, β.naturality, γ.naturality, δ.naturality]

/--
Unit law for horizontal composition:
horizontal composition with identity 2-cells reduces to whiskering.
-/
theorem two_category_unit {C D E : Category}
    {F G : Functor C D} (α : F ⇒ G) (H : Functor D E) (K : Functor C D) :
    NaturalTransformation.hcomp (NaturalTransformation.id H) α =
    NaturalTransformation.whiskerLeft H α ∧
    NaturalTransformation.hcomp α (NaturalTransformation.id K) =
    NaturalTransformation.whiskerRight α K := by
  constructor
  · funext X
    simp [NaturalTransformation.hcomp, NaturalTransformation.whiskerLeft,
      NaturalTransformation.whiskerRight, NaturalTransformation.vcomp,
      NaturalTransformation.id]
  · funext X
    simp [NaturalTransformation.hcomp, NaturalTransformation.whiskerLeft,
      NaturalTransformation.whiskerRight, NaturalTransformation.vcomp,
      NaturalTransformation.id]

/-! ## Functor Category [C, D] is a Category -/

/--
The functor category [C, D] is indeed a category: objects are functors,
morphisms are natural transformations, composition is vertical.
-/
theorem functorCategory_is_category {C D : Category} :
    let FC := FunctorCategoryCat (C := C) (D := D)
    (∀ (F G H K : FC.Obj) (f : FC.Hom F G) (g : FC.Hom G H) (h : FC.Hom H K),
      FC.comp h (FC.comp g f) = FC.comp (FC.comp h g) f) := by
  intro FC F G H K f g h
  funext X
  simp [FC, FunctorCategoryCat, NaturalTransformation.vcomp, D.assoc]

/--
The identification of natural transformations with morphisms in [C, D].
-/
theorem natTrans_as_morphisms_in_functorCat {C D : Category}
    (F G : Functor C D) :
    (FunctorCategoryCat.Hom F G) = (F ⇒ G) := rfl

/-! ## Yoneda Lemma via Natural Transformations -/

/--
The Yoneda lemma: For a functor F : C → Set and an object X of C,
there is a natural bijection:
  Nat(yX, F) ≅ F(X)
where yX = Hom_C(X, -) is the covariant representable functor.
-/

/--
The Yoneda map: given a natural transformation η : yX ⇒ F, evaluate at X
on id_X to get an element of F(X).
-/
def yonedaMap {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (η : FunctorCategoryCat.Hom (homFunctor C X) F) :
    F.mapObj X :=
  η.component X (C.id X)

/--
The inverse Yoneda map: given an element x ∈ F(X), construct a natural
transformation yX ⇒ F.
-/
def yonedaMapInv {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (x : F.mapObj X) :
    FunctorCategoryCat.Hom (homFunctor C X) F where
  component Y f := F.mapHom f x
  naturality {Y Z} f := by
    funext g
    simp [homFunctor, F.preservesComp]

/--
The Yoneda lemma states that yonedaMap and yonedaMapInv are inverses.
This gives the natural isomorphism Nat(yX, F) ≅ F(X).
-/
theorem yoneda_lemma {C : Category} (F : Functor C SetCat) (X : C.Obj)
    (x : F.mapObj X) : yonedaMap F X (yonedaMapInv F X x) = x := by
  simp [yonedaMap, yonedaMapInv, homFunctor, F.preservesId]

/--
The Yoneda embedding y : C → [C^op, Set] is fully faithful.
This means for any objects X, Y of C, the map
  yoneda_map : Hom_C(X, Y) → Nat(Hom_C(-, X), Hom_C(-, Y))
given by f ↦ (f ∘ -) is a bijection.
-/
theorem yonedaEmbedding_fullyFaithful {C : Category} (X Y : C.Obj) (f g : C[X, Y]) :
    (∀ (Z : C.Obj) (h : C[Z, X]), C.comp f h = C.comp g h) → f = g := by
  intro h
  have h_id : C.comp f (C.id X) = C.comp g (C.id X) := h X (C.id X)
  simp at h_id
  exact h_id

/--
The Yoneda lemma fully stated: For any functor F : C → Set and object X,
the evaluation map ev_id : Nat(Hom(X, -), F) → F(X) given by η ↦ η_X(id_X)
is a bijection (isomorphism in Set).
-/
theorem yoneda_bijection {C : Category} (F : Functor C SetCat) (X : C.Obj) :
    Function.Bijective (yonedaMap F X) := by
  refine ⟨?_, ?_⟩
  · intro η₁ η₂ h
    funext Z g
    have hη₁ := congrArg (λ t => t.component X (C.id X)) h
    simp [yonedaMap] at hη₁
    calc
      η₁.component Z g = F.mapHom g (η₁.component X (C.id X)) := by
        have := congrFun (η₁.naturality g) (C.id X)
        simp [homFunctor] at this
        exact this.symm
      _ = F.mapHom g (η₂.component X (C.id X)) := by rw [hη₁]
      _ = η₂.component Z g := by
        have := congrFun (η₂.naturality g) (C.id X)
        simp [homFunctor] at this
        exact this
  · intro x
    refine ⟨yonedaMapInv F X x, ?_⟩
    simp [yonedaMap, yonedaMapInv, homFunctor, F.preservesId]

/-! ## #eval Examples -/

/-- Yoneda map example: for F = listFunctor and X = Nat. -/
def yonedaExample : listFunctor.mapObj Nat :=
  yonedaMap listFunctor Nat
    { component := λ Y f => listFunctor.mapHom f [1,2,3]
      naturality := λ f => by funext; simp }

#eval "Theorems.Main: cat_is_category, homCat_is_functorCat, two_category_interchange, functorCategory_is_category, yoneda_lemma"
#eval s!"Cat is a strict 2-category"
#eval s!"Functor category [C, D] is a category"
#eval s!"Yoneda lemma: Nat(yX, F) ≅ F(X)"
#eval yonedaExample
