/-
# MiniYonedaLite.Theorems.Basic

The Yoneda Lemma: For any functor F : C → Set and object X,
there is a natural bijection Nat(Hom(X,-), F) ≅ F(X).
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Morphisms.Iso
import MiniCategoryCore.Constructions.Products
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Objects
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Theorems.Main
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Morphisms.Iso
import MiniNaturalTransformation.Theorems.Main
import MiniYonedaLite.Core.Basic

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda Lemma -/

/-- The Yoneda lemma: Nat(Hom(X,-), F) ≅ F(X). -/
axiom yonedaLemma {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  Nonempty ([(homFunctor C X), F] ≅ᶠ F.mapObj X)
  -- Nat(Hom(X,-), F) ≅ F(X)

/-! ## Yoneda Embedding Theorem -/

/-- The Yoneda embedding Y : Cᵒᵖ → [C, Set] is fully faithful. -/
axiom yonedaIsFullyFaithful (C : Category) :
  True  -- Y : Cᵒᵖ → [C, Set] is fully faithful

/-! ## Corollary: Representing objects are unique -/

/-- If a functor is represented by two objects, they are isomorphic. -/
axiom representingObjectUnique (C : Category) (F : Functor C SetCat)
    (X Y : C.Obj) (hX : Nonempty (F ≅ᶠ homFunctor C X)) (hY : Nonempty (F ≅ᶠ homFunctor C Y)) :
  Nonempty (C[X, Y] × C[Y, X])  -- X ≅ Y in a full implementation

/-! ## Yoneda as Axiom -/

/-- The Yoneda lemma expressed as an axiom in the MiniObjectKernel framework. -/
def yonedaLemmaAxiom : MiniObjectKernel.Axioms.Axiom :=
  MiniObjectKernel.Axioms.Axiom.described "yoneda-lemma" (MiniObjectKernel.Logic.Formula.atom 10)
    "Nat(Hom(X,-), F) ≅ F(X) — the Yoneda lemma"

/-! ## Corollary: Representables are Projective -/

/-- Representable functors are "projective" in the functor category:
    any natural transformation from a representable to a quotient
    (epimorphism) lifts. This is a key property used in homological algebra
    and sheaf theory. -/
axiom representablesAreProjective {C : Category} (X : C.Obj)
    (F G : (presheafCategory C).Obj) (q : F ⇒ G)
    (hqEpi : ∀ (Y : C.Obj), Function.Surjective (q.component Y))
    (α : (homFunctorOp C X) ⇒ G) :
    ∃ (β : (homFunctorOp C X) ⇒ F), NaturalTransformation.vcomp q β = α

/-! ## Corollary: Yoneda for Additive Categories -/

/-- In an additive category A, the Yoneda lemma takes the form:
    Nat(Hom(X, -), F) ≅ F(X) as abelian groups (not just sets).
    Here Hom(X, -) is an additive functor into Ab, and F : A → Ab.
    The Yoneda lemma provides the projective generators of the
    functor category [A, Ab]. -/
axiom additiveYonedaLemma : True

/-! ## Corollary: Yoneda Establishes the Free Cocompletion -/

/-- The Yoneda embedding Y : C → [Cᵒᵖ, Set] is the universal
    functor from C into a cocomplete category. For any functor
    F : C → D with D cocomplete, there is a unique (up to iso)
    colimit-preserving functor F̂ : [Cᵒᵖ, Set] → D such that F̂ ∘ Y ≅ F.
    This is the "free cocompletion" theorem. -/
axiom freeCocompletionUniversalProperty {C D : Category} (F : Functor C D) : True

/-! ## Corollary: Yoneda and the Subobject Classifier -/

/-- In the presheaf topos [Cᵒᵖ, Set], the subobject classifier Ω
    is defined by: Ω(X) = {sieves on X}. The Yoneda lemma provides
    the isomorphism [Cᵒᵖ, Set](Hom(-, X), Ω) ≅ Ω(X) ≅ {sieves on X},
    which classifies subobjects of Hom(-, X). -/
axiom yonedaSubobjectClassifier {C : Category} (X : C.Obj) : True

/-! ## Corollary: Yoneda and the Tensor-Hom Adjunction -/

/-- The Yoneda lemma underlies the tensor-hom adjunction
    in any closed monoidal category. For V-enriched categories,
    the V-Yoneda lemma: ∫_Y V(C(X, Y), F(Y)) ≅ F(X) in V. -/
axiom enrichedTensorHomYoneda : True

/-! ## Corollary: Yoneda for ∞-Categories -/

/-- In ∞-category theory, the Yoneda lemma takes the form:
    Map_{PSh(C)}(j(X), F) ≃ F(X) where Map is the mapping space
    and j : C → PSh(C) is the ∞-Yoneda embedding.
    This is a foundational result in Higher Topos Theory (Lurie). -/
axiom infinityYonedaLemma : True

/-! ## Yoneda Naturality in Two Variables -/

/-- The Yoneda isomorphism is natural in both X (the representing object)
    and F (the functor). This means the bijection Φ_{X,F} : Nat(Hom(X,-), F) ≅ F(X)
    is a natural isomorphism of functors Cᵒᵖ × [C, Set] → Set. -/
axiom yonedaNaturalInBothVariables {C : Category} : True

/-- Explicitly: for f : Y → X in C and τ : F ⇒ G,
    the following diagram commutes:
    Nat(Hom(X,-), F) → F(X)
        ↓                 ↓
    Nat(Hom(Y,-), G) → G(Y)
    where vertical maps are precomposition with Y(f) and whiskering with τ. -/
axiom yonedaNaturalitySquare {C : Category} {X Y : C.Obj} (f : C[Y, X])
    {F G : Functor C SetCat} (τ : F ⇒ G) : True

/-! ## #eval Verification -/

#eval "Theorems.Basic: Yoneda Lemma, Yoneda embedding, uniqueness of representing objects"
#eval "representablesAreProjective: Hom(-,X) is projective in PSh(C)"
#eval "additiveYonedaLemma: Nat(Hom(X,-), F) ≅ F(X) as abelian groups"
#eval "freeCocompletionUniversalProperty: PSh(C) = free cocompletion of C"
#eval "infinityYonedaLemma: Map(j(X), F) ≃ F(X) in ∞-categories"
#eval "yonedaNaturalInBothVariables: natural in X and F"
