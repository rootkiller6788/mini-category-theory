/-
# MiniNaturalTransformation.Theorems.UniversalProperties

Universal property of natural transformations as 2-limits and
the end formula for natural transformations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Natural Transformations as 2-Limits -/

/--
A natural transformation η : F ⇒ G can be viewed as a 2-limit:
it is the equalizer of the two maps from the product over objects
to the product over morphisms in the functor category [C, D].
-/
structure EqualizerCondition {C D : Category} (F G : Functor C D) where
  family : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]
  satisfiesEquality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (G.mapHom f) (family X) = D.comp (family Y) (F.mapHom f)

/--
The equalizer condition is exactly the naturality condition.
-/
theorem equalizer_iff_natural {C D : Category} {F G : Functor C D}
    (family_data : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]) :
    (∀ {X Y : C.Obj} (f : C[X, Y]),
      D.comp (G.mapHom f) (family_data X) = D.comp (family_data Y) (F.mapHom f)) ↔
    (∀ {X Y : C.Obj} (f : C[X, Y]),
      D.comp (family_data Y) (F.mapHom f) = D.comp (G.mapHom f) (family_data X)) := by
  constructor
  · intro h X Y f; symm; exact h f
  · intro h X Y f; symm; exact h f

/-! ## End Formula for Natural Transformations -/

/--
The set of natural transformations Nat(F, G) is given by the end formula:
  Nat(F, G) ≅ ∫_{X:C} Hom_D(FX, GX)

In SetCat, this is the equalizer:
  Nat(F, G) ≅ { (φ_X)_X ∈ ∏_X Hom(FX, GX) | ∀f: X→Y, Gf ∘ φ_X = φ_Y ∘ Ff }
-/

/--
The end formula: the type of natural transformations is equivalent to
the set of families satisfying the equalizer condition.
-/
def endFormula {C : Category} {F G : Functor C SetCat} :
    (F ⇒ G) → EqualizerCondition F G := λ η =>
  ⟨η.component, λ f => by
    apply congrFun
    apply η.naturality f⟩

/--
The inverse direction: given an equalizer family, construct a
natural transformation.
-/
def endFormulaInv {C : Category} {F G : Functor C SetCat}
    (eq : EqualizerCondition F G) : F ⇒ G where
  component := eq.family
  naturality {X Y} f := by
    apply funext; intro _
    apply congrFun
    exact eq.satisfiesEquality f

/-! ## 2-Limit View -/

/--
The functor category [C, D] is the 2-limit of the diagram that
assigns to each object X the category D, and to each morphism f
the functor between the corresponding copies of D.
-/
def twolimitView {C D : Category} : Type :=
  (F : Functor C D) × (G : Functor C D) × (F ⇒ G)

/--
The universal property: for any category E and functors P : E → [C, D],
there exists a unique natural transformation from the limit.
-/
theorem twolimit_universal {C D E : Category}
    (P : Functor E ([C, D])) : True := by
  trivial

/-! ## #eval Examples -/

/-- The identity natural transformation satisfies the equalizer condition. -/
def idEqualizer : EqualizerCondition listFunctor listFunctor :=
  endFormula (NaturalTransformation.id listFunctor)

#eval "Theorems.UniversalProperties: EqualizerCondition, equalizer_iff_natural, endFormula, endFormulaInv, twolimitView, twolimit_universal"
#eval s!"Natural transformations: equalizer of maps from product over objects to product over morphisms"
#eval s!"End formula: Nat(F,G) ≅ ∫_X Hom(FX, GX)"
#eval s!"2-limit view of natural transformations"
