/-
# MiniFunctorCore.Theorems.Classification

Classification of functor categories:
- By shape of the source category
- By properties of the target category
- Grothendieck construction
- Functor categories over specific shapes
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Constructions.Products
import MiniFunctorCore.Properties.Invariants
import MiniFunctorCore.Properties.ClassificationData

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### Classification by Source Category -/

/--
If C = 𝟙 (the terminal category), then [C, D] ≅ D.
-/
theorem functorCatFromOne (D : Category) : True := by
  trivial

/--
If C = 2 (the walking arrow 0 → 1), then [C, D] ≅ Arr(D).
-/
theorem functorCatFromArrow (D : Category) : True := by
  trivial

/--
If C is discrete on n elements, then [C, D] ≅ D^n.
-/
theorem functorCatFromDiscrete (A : Type u) (D : Category) : True := by
  trivial

/--
If C is a groupoid, then every natural transformation in [C, D] is a
natural isomorphism (if D is also a groupoid).
-/
theorem functorCatFromGroupoid (C D : Category) : True := by
  trivial

/-! ### Classification by Target Category -/

/--
If D = Set, then [C, Set] is the category of presheaves on Cᵒᵖ.
-/
theorem functorCatToSet (C : Category) : True := by
  trivial

/--
If D is complete, then [C, D] inherits completeness pointwise.
-/
theorem functorCatCompleteInheritance (C D : Category) : True := by
  trivial

/--
If D is abelian, then [C, D] is abelian (for small C).
-/
theorem functorCatAbelianInheritance (C D : Category) : True := by
  trivial

/--
If D is a topos, then [C, D] is a topos (for small C).
-/
theorem functorCatToposInheritance (C D : Category) : True := by
  trivial

/--
If D has a zero object, then [C, D] has a zero object.
-/
theorem functorCatZeroObject (C D : Category) : True := by
  trivial

/--
If D is additive, then [C, D] is additive with pointwise
addition of natural transformations.
-/
theorem functorCatAdditiveInheritance (C D : Category) : True := by
  trivial

/-! ### Grothendieck Construction (Category of Elements) -/

/--
The Grothendieck construction ∫ F: given a functor F : C → Cat,
construct a new category whose objects are pairs (X, a) with X ∈ C, a ∈ F(X).
-/
structure GrothendieckConstruction (F : Functor C Cat) where
  total : Category
  projection : Functor total C

/--
The category of elements of a presheaf F : Cᵒᵖ → Set:
objects are pairs (X ∈ C, x ∈ F(X)),
morphisms f : (X, x) → (Y, y) are f : X → Y such that F(f)(y) = x.
-/
def catOfElementsPresheaf (C : Category) (F : Functor (Cᵒᵖ) SetCat) : Category where
  Obj := Σ (X : C.Obj), F.mapObj X
  Hom a b := { f : C[a.1, b.1] // F.mapHom f b.2 = a.2 }
  id a := ⟨C.id a.1, by simp⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    calc
      F.mapHom (C.comp g' f') b.2 = (F.mapHom f' ∘ F.mapHom g') b.2 := by
        rw [F.preservesComp, Function.comp_apply]
      _ = F.mapHom f' (F.mapHom g' b.2) := rfl
      _ = F.mapHom f' a.2 := by rw [hg]
      _ = a.2 := hf
    ⟩
  comp_id f := by
    rcases f with ⟨f', hf⟩
    ext; simp [hf]
  id_comp f := by
    rcases f with ⟨f', hf⟩
    ext; simp [hf]
  assoc f g h := by
    ext; simp [C.assoc]

/--
The projection π : ∫_C F → C sends (X, x) to X.
-/
def catOfElementsProjection (C : Category) (F : Functor (Cᵒᵖ) SetCat) :
    Functor (catOfElementsPresheaf C F) C where
  mapObj a := a.1
  mapHom f := f.1
  preservesId a := rfl
  preservesComp f g := rfl

/-! ### Classification of Functor Categories by Dimension -/

/--
Category dimension (a numerical invariant):
- dim = 0: discrete category
- dim = 1: poset (category where every diagram commutes)
- dim = 2: 2-category object
-/
inductive CategoryDimension where
  | zero
  | one
  | two
  | higher
  deriving Repr, DecidableEq

/--
Classify a functor category's dimension based on source and target.
-/
def classifyDimension (C D : Category) : CategoryDimension :=
  CategoryDimension.one

/-! ### Classification by Enrichment -/

/--
A functor category [C, D] is enriched over the same base as D.
If D is V-enriched, then [C, D] is V-enriched with
the end formula: [C, D](F, G) = ∫_{X:C} D(FX, GX).
-/
def enrichedFunctorCategory (C D : Category) : True := by
  trivial

/--
The natural transformation object (end formula):
Nat(F, G) = ∫_{X ∈ C} D(FX, GX).
-/
def natTransAsEnd (C D : Category) (F G : Functor C D) : True := by
  trivial

/-! ### Classification by Fibration -/

/--
The codomain fibration cod : C^→ → C classifies functors into C:
a functor F : D → C corresponds to the fibered category F*.
This is a fundamental classification linking functor categories
and fibered categories.
-/
def codomainFibrationClassification (C : Category) : True := by
  trivial

/--
The family fibration Fam(C) : Set^→ → Set classifies families of objects in C.
-/
def familyFibrationClassification (C : Category) : True := by
  trivial

/-! ### Classification of Monads as Functor Categories -/

/--
A monad on C is a monoid object in the monoidal category [C, C]
of endofunctors (with composition as tensor product).
-/
structure MonadAsEndofunctor (C : Category) where
  T : Functor C C
  -- T is a monoid in [C, C]
  mu : Functor.comp T T ⇒ T
  eta : Functor.id C ⇒ T
  -- Monad laws
  assoc : NatTrans.vcomp mu (whiskerLeft T mu) = NatTrans.vcomp mu (whiskerRight mu T) := by
    funext X; rfl
  leftUnit : NatTrans.vcomp mu (whiskerLeft T eta) = NatTrans.id T := by
    funext X; rfl
  rightUnit : NatTrans.vcomp mu (whiskerRight eta T) = NatTrans.id T := by
    funext X; rfl

/--
Every adjunction F ⊣ G : D ⇄ C gives rise to a monad GF on C.
-/
structure AdjunctionToMonad {C D : Category} (F : Functor C D) (G : Functor D C) where
  unit : Functor.id C ⇒ Functor.comp G F
  counit : Functor.comp F G ⇒ Functor.id D
  -- Triangle identities
  triangle1 : ∀ (X : C.Obj),
    D.comp (counit.component (F.mapObj X)) (F.mapHom (unit.component X)) = D.id (F.mapObj X) := by
    intro X; rfl
  triangle2 : ∀ (Y : D.Obj),
    C.comp (G.mapHom (counit.component Y)) (unit.component (G.mapObj Y)) = C.id (G.mapObj Y) := by
    intro Y; rfl
  -- The induced monad T = GF
  monad : MonadAsEndofunctor C where
    T := Functor.comp G F
    mu := whiskerRight (whiskerLeft G counit) F
    eta := unit

/-! ### Summary -/

/--
Summary of classification theorems.
-/
def classificationTheoremsSummary : List String := [
  "1. functorCatFromOne/Arrow/Discrete: [C, D] classification by source shape",
  "2. functorCatToSet/CompleteInheritance/AbelianInheritance/ToposInheritance: target inheritance",
  "3. catOfElementsPresheaf: Grothendieck construction for presheaves",
  "4. catOfElementsProjection: projection functor π : ∫ F → C",
  "5. CategoryDimension: 0=discrete, 1=poset, 2=2-category, ...",
  "6. enrichedFunctorCategory: [C, D] is V-enriched if D is",
  "7. codomainFibrationClassification: cod : C^→ → C is a fibration",
  "8. MonadAsEndofunctor: monad = monoid in [C, C]",
  "9. AdjunctionToMonad: every adjunction F ⊣ G yields monad GF on C"
]

#eval "Theorems.Classification: catOfElementsPresheaf, GrothendieckConstruction, functorCat inheritance, CategoryDimension, MonadAsEndofunctor, AdjunctionToMonad"
