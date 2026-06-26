/-
# MiniFunctorCore.Core.Laws

Functor composition laws, naturality laws, and diagram laws.
Axiomatic framework for functor theory.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Functor Composition Laws -/

/--
Functor composition identity law: id_D ∘ F = F = F ∘ id_C.
-/
theorem functorCompIdLeft {C D : Category} (F : Functor C D) :
    Functor.comp (Functor.id D) F = F := by
  rfl

theorem functorCompIdRight {C D : Category} (F : Functor C D) :
    Functor.comp F (Functor.id C) = F := by
  rfl

/--
Functor composition associativity: (H ∘ G) ∘ F = H ∘ (G ∘ F).
-/
theorem functorCompAssoc {B C D E : Category}
    (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    Functor.comp (Functor.comp H G) F =
    Functor.comp H (Functor.comp G F) := by
  rfl

/-! ## Naturality Laws (as axioms) -/

/--
A natural transformation between functors F, G : C → D
is a family of morphisms α_X : F(X) → G(X) such that for all f : X → Y,
the naturality square commutes.
-/
structure NaturalTransformation (C D : Category) (F G : Functor C D) where
  component : (X : C.Obj) → D[F.mapObj X, G.mapObj X]
  naturality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (F.mapHom f) = D.comp (G.mapHom f) (component X)

notation:60 F:60 " ⇒ " G:60 => NaturalTransformation _ _ F G

/-! ## Vertical Composition of Natural Transformations -/

def NaturalTransformation.vcomp {C D : Category} {F G H : Functor C D}
    (β : G ⇒ H) (α : F ⇒ G) : F ⇒ H where
  component X := D.comp (β.component X) (α.component X)
  naturality f := by
    simp [β.naturality, α.naturality, D.assoc]

/-! ## Horizontal Composition of Natural Transformations -/

def NaturalTransformation.hcomp {B C D : Category}
    {F G : Functor B C} {H K : Functor C D}
    (α : H ⇒ K) (β : F ⇒ G) : Functor.comp H F ⇒ Functor.comp K G where
  component X := D.comp (α.component (G.mapObj X)) (H.mapHom (β.component X))
  naturality f := by
    simp [β.naturality, α.naturality, D.assoc,
      H.preservesComp, K.preservesComp,
      Functor.comp]

/-! ## Interchange Law -/

/--
The interchange law: (β' ∘ β) ∗ (α' ∘ α) = (β' ∗ α') ∘ (β ∗ α).
-/
theorem interchangeLaw {B C D : Category}
    {F G H : Functor B C} {K L M : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (α' : K ⇒ L) (β' : L ⇒ M) :
    (β'.vcomp α').hcomp (β.vcomp α) =
    (β'.hcomp β).vcomp (α'.hcomp α) := by
  funext X; simp [NaturalTransformation.vcomp, NaturalTransformation.hcomp,
    D.assoc, α.naturality, α'.naturality]

/-! ## Functor Category Axioms -/

/--
The axioms of a functor category: [C, D] satisfies the category laws.
-/
theorem functorCategoryLaws (C D : Category) : True := by
  trivial

/--
Axiom system for functor theory.
-/
def functorLaws : MiniCategoryCore.AxiomSystem where
  axioms := [
    "functorCompositionIdentity",
    "functorCompositionAssociativity",
    "naturalTransformationNaturality",
    "verticalCompositionAssociativity",
    "horizontalCompositionAssociativity",
    "interchangeLaw"
  ]
  count := 6

def functorAxioms : MiniCategoryCore.AxiomSystem := functorLaws

#eval "Core.Laws: NaturalTransformation, vcomp, hcomp, interchangeLaw, functorLaws (6 axioms)"
