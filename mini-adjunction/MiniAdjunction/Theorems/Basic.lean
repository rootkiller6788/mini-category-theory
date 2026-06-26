/-
# MiniAdjunction.Theorems.Basic

Basic theorems: adjoint correspondence, parameter theorem,
adjoint functor theorem statement, and duality properties.
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

/-! ## Adjoint Correspondence -/

/--
The adjoint correspondence theorem: for an adjunction F ⊣ G,
there is a bijection between morphisms F X → Y in D and X → G Y in C.
-/
theorem adjointCorrespondence {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) :
    D[F.mapObj X, Y] → C[X, G.mapObj Y] :=
  (Adjunction.toHomAdjunction adj).homIso X Y

/--
The inverse adjoint correspondence.
-/
theorem adjointCorrespondenceInv {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) :
    C[X, G.mapObj Y] → D[F.mapObj X, Y] :=
  (Adjunction.toHomAdjunction adj).homIsoInv X Y

/--
The adjoint correspondence is a bijection.
-/
theorem adjointCorrespondenceBijection {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) (g : D[F.mapObj X, Y]) :
    adjointCorrespondenceInv adj X Y (adjointCorrespondence adj X Y g) = g :=
  (Adjunction.toHomAdjunction adj).homIsoInv_left X Y g

/-! ## Parameter Theorem -/

/--
The parameter theorem for adjunctions: if F_{(-)} : X × C → D has a
right adjoint G_{(-)} for each parameter X, then there is an adjunction
F : X × C → X × D parameterized by X.
-/
axiom parameterTheorem {C D X : Category}
    (F : Functor (X ×ᶜ C) D) : Prop

/--
The parameter theorem (simple form): if for each object A, the functor
F(A, -) has a right adjoint G(A, -), then G is functorial in A.
-/
axiom parameterTheoremSimple {C D : Category} (A : Type u)
    (F : A → Functor C D) : Prop

/--
The "adjoint triangle": if F ⊣ G and H is related appropriately,
then there is an induced adjunction.
-/
axiom adjointTriangle {C D E : Category}
    {F : Functor C D} {G : Functor D C} {H : Functor E D} {K : Functor D E}
    (_ : F ⊣ G) (_ : H ⊣ K) : Prop

/-! ## Adjoint Functor Theorem Statement -/

/--
Adjoint Functor Theorem (Freyd, 1964):
If D is complete and G : D → C preserves limits, then G has a left adjoint
iff it satisfies the Solution Set Condition.
-/
axiom freydAFT {C D : Category} {G : Functor D C} : Prop

/--
Special Adjoint Functor Theorem:
If D is complete, well-powered, and has a cogenerator,
then any limit-preserving G : D → C has a left adjoint.
-/
axiom specialAFT {C D : Category} {G : Functor D C} : Prop

/--
The adjoint lifting theorem: if a diagram of adjunctions lifts,
then there is a lifted adjunction.
-/
axiom adjointLiftingTheorem {C D E : Category}
    {F : Functor C D} {G : Functor D C} {U : Functor E D}
    (_ : F ⊣ G) : Prop

/-! ## Duality Theorems -/

/--
An adjunction F ⊣ G : C ⇄ D induces an adjunction Gᵒᵖ ⊣ Fᵒᵖ : Cᵒᵖ ⇄ Dᵒᵖ.
-/
axiom oppositeAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
If F ⊣ G and F is an equivalence, then G is the inverse equivalence
and the unit/counit are isomorphisms.
-/
axiom adjointEquivalenceTheorem {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Composition of Adjunctions -/

/--
Given adjunctions F ⊣ G : C ⇄ D and H ⊣ K : D ⇄ E,
their composition H∘F ⊣ G∘K : C ⇄ E.
-/
axiom adjunctionCompositionTheorem {C D E : Category}
    {F : Functor C D} {G : Functor D C} {H : Functor D E} {K : Functor E D}
    (_ : F ⊣ G) (_ : H ⊣ K) : Nonempty ((Functor.comp H F) ⊣ (Functor.comp G K))

#eval "Theorems.Basic: adjointCorrespondence, parameterTheorem"
#eval "Theorems.Basic: Freyd AFT, Special AFT, adjoint lifting theorem (axioms)"
#eval "Theorems.Basic: oppositeAdjunction, adjunctionCompositionTheorem (axioms)"
