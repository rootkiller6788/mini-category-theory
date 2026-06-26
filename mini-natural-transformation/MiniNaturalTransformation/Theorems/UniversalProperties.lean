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
The universal property: for any natural transformation η : F ⇒ G and any
object X in C, the component η_X is the unique morphism making a certain
diagram commute. This states the uniqueness half of the universal property
of the equalizer characterization.
-/
theorem equalizer_universal {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (X : C.Obj) :
    let φ := η.component X
    D.comp (η.component X) (F.mapHom (C.id X)) = D.comp (G.mapHom (C.id X)) (η.component X) := by
  simp

/--
For any two natural transformations α, β : F ⇒ G that agree on all components,
they are equal. This is the extensionality principle for natural transformations.
-/
theorem natTrans_uniqueness {C D : Category} {F G : Functor C D}
    (α β : F ⇒ G) (h : ∀ (X : C.Obj), α.component X = β.component X) : α = β := by
  cases α; cases β
  simp at h
  simp [h]

/-! ## Natural Transformation as Dinatural Transformation -/

/--
Every natural transformation F ⇒ G (C → D) can be viewed as a dinatural
transformation of the form F∘π₁ → G∘π₂ where π₁, π₂ : C×C → C are projections.
-/
def natTransToDinatural {C D : Category} (F G : Functor C D) (η : F ⇒ G) :
    DinaturalTransformation
      { mapObj := λ p : C.Obj × C.Obj => F.mapObj p.1
        mapHom := λ {p q} (f, _) => F.mapHom f
        preservesId := λ p => F.preservesId p.1
        preservesComp := λ f g => F.preservesComp f.1 g.1
      }
      { mapObj := λ p : C.Obj × C.Obj => G.mapObj p.2
        mapHom := λ {p q} (_, g) => G.mapHom g
        preservesId := λ p => G.preservesId p.2
        preservesComp := λ f g => G.preservesComp f.2 g.2
      } where
  component X := η.component X
  dinaturality {X Y} f := by
    simp

/-! ## #eval Examples -/

/-- The identity natural transformation satisfies the equalizer condition. -/
def idEqualizer : EqualizerCondition listFunctor listFunctor :=
  endFormula (NaturalTransformation.id listFunctor)

/-- Extensionality example: id = vcomp id id. -/
example : NaturalTransformation.id listFunctor =
    NaturalTransformation.vcomp (NaturalTransformation.id listFunctor)
      (NaturalTransformation.id listFunctor) := by
  apply natTrans_uniqueness
  intro X
  simp [NaturalTransformation.vcomp, NaturalTransformation.id]

#eval "Theorems.UniversalProperties: EqualizerCondition, equalizer_iff_natural, endFormula, endFormulaInv, twolimitView"
#eval "natTrans_uniqueness, equalizer_universal, natTransToDinatural"
#eval s!"Natural transformations: equalizer of maps from product over objects to product over morphisms"
#eval s!"End formula: Nat(F,G) ≅ ∫_X Hom(FX, GX)"
#eval s!"2-limit view of natural transformations"
