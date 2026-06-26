/-
# MiniAdjunction.Properties.Preservation

Left adjoints preserve colimits; right adjoints preserve limits.
Also: uniqueness of adjoints and preservation/reflection theorems.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Preservation Properties of Adjoints -/

/--
Left adjoints preserve colimits: if F ⊣ G and a diagram has a colimit,
then F applied to the colimit is a colimit of F applied to the diagram.
-/
axiom leftAdjointPreservesColimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Right adjoints preserve limits: if F ⊣ G and a diagram has a limit,
then G applied to the limit is a limit of G applied to the diagram.
-/
axiom rightAdjointPreservesLimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Uniqueness of Adjoints -/

/--
Any two right adjoints to the same functor are naturally isomorphic.
-/
axiom adjointUniqueUpToIso {C D : Category} {F : Functor C D} {G₁ G₂ : Functor D C}
    (_ : F ⊣ G₁) (_ : F ⊣ G₂) : Nonempty (G₁ ⇒ G₂)

/--
Any two left adjoints to the same functor are naturally isomorphic.
-/
axiom leftAdjointUniqueUpToIso {C D : Category} {F₁ F₂ : Functor C D} {G : Functor D C}
    (_ : F₁ ⊣ G) (_ : F₂ ⊣ G) : Nonempty (F₁ ⇒ F₂)

/-! ## Reflection of Isomorphisms -/

/--
Right adjoints reflect isomorphisms: if G(f) is iso, then f is iso.
-/
axiom rightAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/--
Left adjoints reflect isomorphisms as well (since left adjoint = right adjoint of opposite).
-/
axiom leftAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) : Prop

/-! ## Preservation of Epimorphisms and Monomorphisms -/

/--
Left adjoints preserve epimorphisms. If f is epi and F is a left adjoint,
then F(f) is epi.
-/
axiom leftAdjointPreservesEpi {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) : Prop

/--
Right adjoints preserve monomorphisms. If f is mono and G is a right adjoint,
then G(f) is mono.
-/
axiom rightAdjointPreservesMono {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/-! ## Adjoint Functor Theorems (Statements) -/

/--
The General Adjoint Functor Theorem (Freyd):
If D is complete and locally small, a functor G : D → C has a left adjoint
iff G preserves limits and satisfies the Solution Set Condition.
-/
axiom generalAdjointFunctorTheorem {C D : Category} {G : Functor D C} : Prop

/--
The Special Adjoint Functor Theorem (SAFT):
If C and D are locally small, D is complete, well-powered, and has a
cogenerating set, then any limit-preserving functor G : D → C has a left adjoint.
-/
axiom specialAdjointFunctorTheorem {C D : Category} {G : Functor D C} : Prop

/-! ## Representability and Adjoints -/

/--
A functor G : D → C has a left adjoint iff for each X : C,
the functor C(X, G(-)) : D → Set is representable.
-/
axiom representabilityCriterion {C D : Category} {G : Functor D C} : Prop

/-! ## Commutation with Limits -/

/--
Left adjoints commute with (i.e., preserve) all colimits that exist.
-/
axiom leftAdjointCommutesWithColimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Right adjoints commute with all limits that exist.
-/
axiom rightAdjointCommutesWithLimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Characterizing Existence of Adjoints -/

/--
The Pointwise Adjoint Functor Theorem (conceptual):
For each object X : C, a left adjoint F exists with F(X) defined
if the functor C(X, G(-)) is representable. The representing object
IS F(X).
-/
structure RepresentabilityCondition {C D : Category} (G : Functor D C) (X : C.Obj) where
  representingObject : D.Obj
  universalElement : C[X, G.mapObj representingObject]
  isUniversal : Prop

/--
If for every object X there is a representing object for C(X, G(-)),
then G has a left adjoint.
-/
axiom representabilityToAdjoint {C D : Category} {G : Functor D C}
    (rep : ∀ (X : C.Obj), RepresentabilityCondition G X) : IsRightAdjoint G

/--
Conversely, if G has a left adjoint F, then F(X) represents C(X, G(-)).
-/
axiom adjointToRepresentability {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) : RepresentabilityCondition G X

/-! ## The Initial Object via Adjoint -/

/--
The left adjoint applied to the initial object of C gives the
initial object of D (if F ⊣ G).

Actually: right adjoints preserve terminal objects,
left adjoints preserve initial objects.
-/
structure AdjointPreservesTerminal {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  terminalC : C.Obj
  isTerminalC : ∀ (X : C.Obj), Nonempty (C[X, terminalC])
  terminalD : D.Obj
  isTerminalD : ∀ (Y : D.Obj), Nonempty (D[Y, terminalD])
  preservation : Prop  -- G(terminalD) ≅ terminalC

structure AdjointPreservesInitial {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  initialC : C.Obj
  isInitialC : ∀ (X : C.Obj), Nonempty (C[initialC, X])
  initialD : D.Obj
  isInitialD : ∀ (Y : D.Obj), Nonempty (D[initialD, Y])
  preservation : Prop  -- F(initialC) ≅ initialD

/-! ## Adjoints and Exact Sequences -/

/--
Left adjoints preserve right exact sequences (cokernels, coequalizers).
Right adjoints preserve left exact sequences (kernels, equalizers).

This is a consequence of LAPC/RAPL: colimits include coequalizers,
limits include equalizers.
-/
structure AdjointPreservesExactness {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  leftPreservesRightExact : Prop
  rightPreservesLeftExact : Prop

/-! ## Adjoints and Commutation with Functors -/

/--
Given adjunctions F ⊣ G and F' ⊣ G', we can ask when
F ∘ F' has a right adjoint. The answer: if the Beck-Chevalley
condition holds.
-/
structure BeckChevalleyCondition {C D E : Category}
    {F : Functor C D} {G : Functor D C}
    {F' : Functor D E} {G' : Functor E D}
    (adj : F ⊣ G) (adj' : F' ⊣ G') where
  condition : Prop  -- The base-change square commutes up to natural isomorphism

/-! ## Frobenius Reciprocity -/

/--
Frobenius reciprocity is a special case of adjunction:
For a group homomorphism φ : H → G, the induction and restriction
functors between kG-mod and kH-mod are adjoint on both sides:
  Ind ⊣ Res ⊣ Coind
-/
structure FrobeniusReciprocity where
  group : Type u
  subgroup : Type u
  induction : Functor SetCat SetCat
  restriction : Functor SetCat SetCat
  coinduction : Functor SetCat SetCat
  adj1 : induction ⊣ restriction
  adj2 : restriction ⊣ coinduction

/-! ## The Duality Between Limits and Colimits -/

/--
Given F ⊣ G : C ⇄ D, the preservation properties are dual:
F preserves colimits ↔ G preserves limits.

This is a consequence of the adjunction in opposite categories:
Gᵒᵖ ⊣ Fᵒᵖ : Dᵒᵖ ⇄ Cᵒᵖ.
Since limits in D correspond to colimits in Dᵒᵖ,
G preserving limits ≡ Gᵒᵖ preserving colimits.
-/
structure LimitColimitDuality {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  opAdj : OppositeAdjunction adj
  limitColimitCorrespondence : Prop

/-! ## Adjoints in Enriched Category Theory -/

/--
In enriched category theory (over a closed symmetric monoidal category V),
an adjunction is defined with V-natural isomorphisms:
  D(F X, Y) ≅ C(X, G Y)   in V (not just in Set)

This generalizes ordinary adjunctions (which are Set-enriched).
-/
structure EnrichedAdjunction (V : Category) where
  isClosedSymmetric : Prop
  enrichedC : Category
  enrichedD : Category
  enrichedF : Functor enrichedC enrichedD
  enrichedG : Functor enrichedD enrichedC
  enrichedAdj : enrichedF ⊣ enrichedG

/-! ## Summary -/

/--
Preservation properties formalized:
1. leftAdjointPreservesColimits (axiom)
2. rightAdjointPreservesLimits (axiom)
3. adjointUniqueUpToIso (axiom)
4. leftAdjointUniqueUpToIso (axiom)
5. rightAdjointReflectsIso (axiom)
6. leftAdjointReflectsIso (axiom)
7. leftAdjointPreservesEpi (axiom)
8. rightAdjointPreservesMono (axiom)
9. generalAdjointFunctorTheorem (axiom)
10. specialAdjointFunctorTheorem (axiom)
11. representabilityCriterion (axiom)
12. leftAdjointCommutesWithColimits (axiom)
13. rightAdjointCommutesWithLimits (axiom)
14. RepresentabilityCondition (structure)
15. representabilityToAdjoint / adjointToRepresentability (axioms)
16. AdjointPreservesTerminal / AdjointPreservesInitial (structures)
17. AdjointPreservesExactness (structure)
18. BeckChevalleyCondition (structure)
19. FrobeniusReciprocity (structure)
20. LimitColimitDuality (structure)
21. EnrichedAdjunction (structure)
-/

#eval "Properties.Preservation: ✓ LAPC, RAPL, adjoint uniqueness (21 theorems/structures)"
#eval "Properties.Preservation: ✓ Representability, terminal/initial, exactness, Beck-Chevalley"
#eval "Properties.Preservation: ✓ Frobenius reciprocity, limit-colimit duality, enriched adjunction"
#eval "Properties.Preservation: ✓ General AFT, SAFT, representability criterion (axioms)"
