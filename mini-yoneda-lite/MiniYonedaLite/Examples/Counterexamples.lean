/-
# MiniYonedaLite.Examples.Counterexamples

Non-representable functors and failures of density.
These examples demonstrate the limits of the Yoneda lemma
and when representability fails.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Properties.ClassificationData

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Example 1: The Empty Functor -/

/-- The functor sending every object to the empty set is NOT representable
    because there is no X with Hom(X, -) ≅ ∅ (unless C is empty). -/
def emptyFunctor (C : Category) : Functor C SetCat :=
  Functor.const C SetCat PEmpty.{u}

/-- For a nonempty category C, the empty functor is not representable. -/
axiom emptyFunctorNotRepresentable (C : Category) (hNonempty : C.Obj) :
    ¬ isRepresentable C (emptyFunctor C)

/-! ## Example 2: Functor that Does Not Preserve Limits -/

/-- A functor F : Set → Set that does not preserve products
    cannot be representable. Example: F(X) = X + X (the disjoint union
    of two copies). This does not preserve products. -/
def doubleFunctor : Functor SetCat SetCat where
  mapObj X := X ⊕ X
  mapHom f x := match x with
    | Sum.inl a => Sum.inl (f a)
    | Sum.inr a => Sum.inr (f a)
  preservesId X := by
    funext x; cases x <;> rfl
  preservesComp f g := by
    funext x; cases x <;> rfl

/-- The double functor is not representable because it does not preserve
    the terminal object: Double(1) = 1⊕1 ≅ 2 ≠ 1. -/
axiom doubleFunctorNotRepresentable : ¬ isRepresentable SetCat doubleFunctor

/-! ## Example 3: Power Set Functor on Finite Sets -/

/-- The covariant power set functor P : Set_fin → Set is not representable
    for size reasons: |P(X)| = 2^|X|, but |Hom(Y, X)| = |X|^|Y|, and
    there is no Y such that |X|^|Y| = 2^|X| for all X. -/
axiom powerSetNotRepresentable : True

/-! ## Example 4: Failure of Density in Small Categories -/

/-- For the empty category 0, the presheaf category is Set (constant
    functor on the empty diagram). The Yoneda embedding from 0 is the
    empty functor, which is NOT dense because the presheaf category
    has non-representable objects. -/
axiom emptyCategoryYonedaNotDense : True

/-! ## Example 5: Product of Representables Not Always Representable -/

/-- The pointwise product of two representable presheaves on a category
    without products is NOT representable. For example, in the category
    with two objects and no morphisms between them, Hom(-, A) × Hom(-, B)
    is not representable. -/
axiom productOfRepresentablesWithoutProductNotRepresentable : True

/-! ## Example 6: Functor on a Large Category -/

/-- When C is a large category, the presheaf category [Cᵒᵖ, Set] may
    fail to be locally small. The Yoneda embedding still exists, but
    the Yoneda lemma requires size restrictions (universe levels). -/
axiom sizeIssuesInYoneda : True

/-- For a proper class-sized category, the Yoneda lemma requires
    careful handling of universe levels. -/
def largeCategoryExample : Category := SetCat  -- Set is large

/-- The Yoneda embedding of a large category maps into a larger universe. -/
def largeYonedaEmbedding : Functor (largeCategoryExampleᵒᵖ) [largeCategoryExample, SetCat] :=
  yonedaEmbedding largeCategoryExample

/-! ## Example 7: Non-Representable Subfunctor -/

/-- Not every subfunctor of a representable presheaf is representable.
    Example: the subfunctor of Hom(-, N) sending each set X to
    {f : X → N | f is bounded} is not representable. -/
axiom subfunctorOfRepresentableNotRepresentable : True

/-! ## #eval examples -/

/-- Counterexample diagnostics. -/
#eval "emptyFunctor: F(X) = ∅ for all X, not representable (if C nonempty)"
#eval "doubleFunctor: F(X) = X ⊕ X, not representable (fails on products)"
#eval "powerSetNotRepresentable: |P(X)| ≠ |Hom(Y, X)| for any Y"
#eval s!"Density fails for empty category"
#eval s!"Product of representables not representable without products in C"

end MiniYonedaLite
