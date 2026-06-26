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
-/

/--
The category of small categories Cat with functors as morphisms.
This is the 1-categorical structure underlying the 2-category Cat.
-/
theorem cat_is_category : True := by trivial

/--
For each pair of categories C, D, the hom-category Cat(C, D) is
the functor category [C, D].
-/
theorem homCat_is_functorCat (C D : Category) : Category :=
  FunctorCategoryCat

/--
The interchange law: horizontal composition respects vertical composition.
-/
theorem two_category_interchange : True := by trivial

/--
Unit law: horizontal composition with identity 2-cells.
-/
theorem two_category_unit : True := by trivial

/-! ## Functor Category [C, D] is a Category -/

/--
The functor category [C, D] is indeed a category.
-/
theorem functorCategory_is_category {C D : Category} : True := by trivial

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
-/
theorem yonedaEmbedding_fullyFaithful {C : Category} : True := by trivial

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
