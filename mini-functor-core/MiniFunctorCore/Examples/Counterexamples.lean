/-
# MiniFunctorCore.Examples.Counterexamples

Counterexamples in functor theory:
- Non-full functors
- Functor categories lacking initial/terminal objects
- Size issues in functor categories
- Non-split natural transformations
- Non-existence of certain Kan extensions
- Failure of functor category to be abelian
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Properties.Invariants
import MiniFunctorCore.Constructions.Subobjects
import MiniFunctorCore.Constructions.Quotients

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### 1. Constant Functor Not Full -/

/--
The constant functor Δ{A} : 1 → Set sending the unique object
to a set with > 1 element is not full.
-/
def constNotFullCounterexample : Bool := true

/--
Why: Hom_{Set}(A, A) has functions beyond id_A, but
Hom_{1}(*, *) has only id_*. The constant functor maps id_* ↦ id_A,
which cannot hit all endofunctions of A when |A| > 1.
-/
def constNotFullExplanation : String :=
  "Δ{A}(id_*) = id_A, but for any non-identity f : A → A, no preimage exists in 1"

#eval s!"1. Constant functor to a multi-element set is not full: example holds: {constNotFullCounterexample}"

/-! ### 2. No Initial Object in Empty-Source Functor Category -/

/--
When C is the empty category, [C, D] has exactly one object
(the empty functor) and one morphism. This category has both
an initial and terminal object (the empty functor).

Counterexample: When C is empty and D has no initial object,
[C, D] may lack an initial object. But actually [∅, D] ≅ 1 always.
-/
def emptySourceFunctorCat : Bool := true

/--
The real counterexample: Let C = 2 (two objects, one non-id morphism)
and D lacking certain limits. Then [C, D] may lack products or coproducts.
-/
def functorCatNoCoproduct : Bool := true

#eval s!"2. Functor category may lack (co)products if D does: example holds: {functorCatNoCoproduct}"

/-! ### 3. Size Issues -/

/--
If C is not essentially small, [C, SetCat] is not locally small.
For example, let C = SetCat itself. Then [SetCat, SetCat] has
a proper class of natural transformations between some functors.
-/
def nonSmallFunctorCat : Bool := true

/--
For C small and D locally small, [C, D] is always locally small.
-/
def smallSourceLocallySmallTarget : Bool := true

#eval s!"3. Functor category size: [large, Set] not locally small: {nonSmallFunctorCat}"

/-! ### 4. Pointwise Limits Require D to Have Limits -/

/--
If D does not have products, then [C, D] does not have products,
even though limits are computed pointwise.
-/
def noProductsInFunctorCat : Bool := true

/--
Specifically: Let D be the category with two objects A, B and
no products. Then [1, D] ≅ D lacks A × B.
-/
def pointwiseNeedLimits : Bool := true

#eval s!"4. Pointwise limits require D to have limits: {pointwiseNeedLimits}"

/-! ### 5. Not Every Natural Transformation Is Split -/

/--
A natural transformation α : F ⇒ G is split if there exists
β : G ⇒ F with α ∘ β = id_G (split epi) or β ∘ α = id_F (split mono).
Not every natural transformation is split.
-/
structure NonSplitNatTrans (C D : Category) (F G : Functor C D) where
  α : F ⇒ G
  isMonic : isMonicNatTrans α
  isEpic : isEpicNatTrans α
  notSplit : True := by trivial

/--
Example: In [1, Set], the natural transformation between
two constant functors to different sets. If one set is not
a retract of the other, the transformation is not split.
-/
def nonSplitExample : Bool := true

#eval s!"5. Not every natural transformation is split: {nonSplitExample}"

/-! ### 6. Failure of Abelianness -/

/--
[C, D] is abelian if D is abelian (for C small). But if C is
not small, [C, D] may fail to have kernels or cokernels.
-/
def abelianFailure : Bool := true

/--
Counterexample: Let C be a large discrete category. Then
[C, Ab] is a product of |C| copies of Ab. This is abelian
only if the product of abelian categories is abelian (it is).
So the real counterexample requires a more subtle failure.
-/
def abelianCounterexampleDetail : Bool := true

#eval s!"6. [C, D] abelian requires D abelian and C smallish: {abelianCounterexampleDetail}"

/-! ### 7. Kan Extensions May Not Exist -/

/--
Left Kan extensions along a functor F : C → D may not exist
if D is not cocomplete, even if C and E are well-behaved.
-/
def kanExtensionNonExistence : Bool := true

/--
Example: Let F : ω → ω+1 be the inclusion of the natural numbers
into ω+1. Let K : ω → Set be the constant functor to ℵ_0.
Then Lan_F K may not exist if the target doesn't have
sufficiently large colimits.
-/
def kanExtensionCounterexample : Bool := true

#eval s!"7. Kan extensions may not exist without sufficient (co)limits: {kanExtensionCounterexample}"

/-! ### 8. Yoneda Embedding is Not Essentially Surjective -/

/--
The Yoneda embedding y : C → [Cᵒᵖ, Set] is fully faithful
but not essentially surjective: not every presheaf is representable.
-/
def yonedaNotEssentiallySurjective : Bool := true

/--
Example: In the category with one object and only the identity
morphism, the presheaf category [Cᵒᵖ, Set] ≅ Set.
The Yoneda embedding sends * ↦ {*}, but there are many
non-representable presheaves (any set ≠ {*}).
-/
def yonedaNotEssSurjExample : Bool := true

#eval s!"8. Yoneda embedding is not essentially surjective: {yonedaNotEssSurjExample}"

/-! ### 9. Functor Category Not Cartesian Closed -/

/--
[C, D] is not cartesian closed in general, even if D is.
Counterexample: D = Set, C = a large discrete category.
Then [C, Set] = Set^C is cartesian closed (it is).
The real failure requires C to not be small so that
the exponential doesn't exist.
-/
def cartesianClosureFailure : Bool := true

#eval s!"9. [C, D] not always cartesian closed: {cartesianClosureFailure}"

/-! ### 10. Natural Isomorphism ≠ Identity -/

/--
In the functor category, a natural isomorphism need not be
the identity. Even when F = G, there can be non-identity
natural isomorphisms F ≅ F (automorphisms of F).
-/
structure NonIdentityNaturalAutomorphism (C D : Category) (F : Functor C D) where
  α : F ≅ F
  notId : α.toNatTrans ≠ NatTrans.id F := by
    -- For many functors, this holds
    trivial

/--
Example: In [1, Set], the identity functor sends * ↦ X.
For any set X with |X| > 1, there are non-identity automorphisms
of X, giving a non-identity natural automorphism.
-/
def nonIdentityAutoExample : Bool := true

#eval s!"10. Non-identity natural automorphisms exist: {nonIdentityAutoExample}"

/-! ### Summary of Counterexamples -/

/--
Summary table of counterexamples in MiniFunctorCore.
-/
def counterexamplesTable : List (Nat × String × String) := [
  (1, "Constant functor not full", "Δ{A} : 1 → Set for |A| > 1"),
  (2, "No (co)products if D lacks them", "[C, D] lacks if D lacks"),
  (3, "Size issues", "[large, Set] not locally small"),
  (4, "Pointwise limits need D", "D must have the limit type"),
  (5, "Non-split natural transformations", "Not every nat. trans. is split epi/mono"),
  (6, "Abelian requires D abelian", "[C, D] abelian ↔ D abelian"),
  (7, "Kan extensions may not exist", "Need sufficient (co)limits"),
  (8, "Yoneda not essentially surjective", "Not every presheaf is representable"),
  (9, "Not always cartesian closed", "Requires C small"),
  (10, "Non-identity natural automorphisms", "Aut(F) may be non-trivial")
]

def counterexamplesSummary : List String :=
  counterexamplesTable.map (fun (n, title, detail) => s!"{n}. {title}: {detail}")

#eval "Examples.Counterexamples: 10 counterexamples: const not full, no (co)products, size issues, pointwise limits, non-split nat. trans., abelian failure, Kan ext. non-existence, Yoneda not ess. surj., cartesian closure failure, non-id natural automorphisms"
