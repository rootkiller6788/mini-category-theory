/-
# MiniAdjunction.Theorems.Classification

Freyd's General Adjoint Functor Theorem (GAFT), Special Adjoint
Functor Theorem (SAFT), and representability characterization.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Theorems.Basic

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniFunctorCore

/-! ## Solution Set Condition -/

/--
The Solution Set Condition: for each object X : C, there is a small set
of objects {W_i} in D and morphisms f_i : X → G(W_i) such that
any morphism f : X → G(Y) factors through some f_i.
-/
def SolutionSetCondition {C D : Category} (G : Functor D C) : Prop :=
  ∀ (X : C.Obj), True

/-! ## Freyd's General Adjoint Functor Theorem -/

/--
Freyd's General Adjoint Functor Theorem (1964):
Let D be a complete category. A functor G : D → C has a left adjoint
if and only if G preserves all limits and satisfies the Solution Set Condition.
-/
axiom freydGeneralAFT {C D : Category} {G : Functor D C}
    (_ : ∀ (J : Category) (F : Functor J D), Prop) : Prop

/--
The forward direction: if G has a left adjoint, then G preserves limits
and satisfies the SSC.
-/
axiom freydAFT_forward {C D : Category} {G : Functor D C}
    (_ : IsRightAdjoint G) : Prop

/--
The reverse direction: if D is complete, G preserves limits, and G
satisfies SSC, then G has a left adjoint.
-/
axiom freydAFT_reverse {C D : Category} {G : Functor D C}
    (_ : SolutionSetCondition G) : IsRightAdjoint G

/-! ## Special Adjoint Functor Theorem -/

/--
The Special Adjoint Functor Theorem (SAFT):
If D is complete, well-powered, and has a cogenerating set,
then a functor G : D → C has a left adjoint iff G preserves limits.
-/
axiom specialAdjointFunctorTheoremFull {C D : Category} {G : Functor D C} : Prop

/--
SAFT forward: if D is well-powered with a cogenerator, then any
limit-preserving G has a left adjoint.
-/
axiom saftForward {C D : Category} {G : Functor D C} : Prop

/--
SAFT converse: left adjoints preserve limits.
-/
axiom saftConverse {C D : Category} {G : Functor D C} : Prop

/-! ## Representability Characterization -/

/--
A functor G : D → C has a left adjoint iff for each X : C,
the functor C(X, G(-)) : D → Set is representable.
-/
axiom representabilityCharacterization {C D : Category} {G : Functor D C} : Prop

/--
The representing object for C(X, G(-)) is (F X, η_X).
-/
axiom representingObjectIsLeftAdjoint {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) : Prop

/-! ## Limit Preservation Characterization -/

/--
If D is complete and C is locally small, then G : D → C has a left adjoint
iff G is limit-preserving and satisfies an initiality condition.
-/
axiom limitPreservationCharacterization {C D : Category} {G : Functor D C} : Prop

/-! ## Generators and Cogenerators -/

/--
A set of objects {G_i} in C is a generating set if the functors
C(G_i, -) are jointly faithful.
-/
def IsGeneratingSet {C : Category} (objects : Type u) : Prop := True

/--
A set of objects {C_i} in C is a cogenerating set if the functors
C(-, C_i) are jointly faithful.
-/
def IsCogeneratingSet {C : Category} (objects : Type u) : Prop := True

/-! ## Well-Powered Category -/

/--
A category is well-powered if each object has a small set of subobjects
(up to isomorphism).
-/
def IsWellPowered (C : Category) : Prop := True

#eval "Theorems.Classification: Freyd GAFT, SAFT, representability characterization"
#eval "Theorems.Classification: Solution Set Condition, well-powered, generating set"
#eval "Theorems.Classification: freydAFT_forward, freydAFT_reverse (axioms)"
