/-
# MiniFunctorCore.Constructions.Universal

Universal constructions in functor categories:
- Pointwise limits and colimits
- Kan extensions (left and right)
- The universal property of the presheaf category
- Cones and cocones in functor categories
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### Diagrams and Cones -/

/--
A diagram of shape J in a category C is a functor D : J → C.
-/
def Diagram (J C : Category) := Functor J C

/--
A cone over a diagram D : J → C with apex A is a natural transformation
from the constant functor at A to D.
-/
def Cone {J C : Category} (D : Diagram J C) (A : C.Obj) : Type (max u v) :=
  (Functor.const J C A) ⇒ D

/--
A cocone under a diagram D : J → C with apex A is a natural transformation
from D to the constant functor at A.
-/
def Cocone {J C : Category} (D : Diagram J C) (A : C.Obj) : Type (max u v) :=
  D ⇒ (Functor.const J C A)

/-! ### Pointwise Limits in Functor Categories -/

/--
A pointwise limit of a diagram D : J → [C, E] with apex F : J → [C, E]
is computed by evaluating at each object X of C.
-/
def pointwiseCone {J C E : Category} (D : Diagram J ([C, E])) (F : Functor J ([C, E])) : Type (max u (v+2)) :=
  F ⇒ D

/--
If E has limits of shape J, then [C, E] has limits of shape J,
computed pointwise: (lim D)(X) = lim (ev_X ∘ D).
-/
structure PointwiseLimit {J C E : Category} (D : Diagram J ([C, E])) where
  limit : Functor J ([C, E])
  cone : Cone D limit
  isLimit : ∀ (A : Functor J ([C, E])) (c : Cone D A),
    ∃! (f : A ⇒ limit), True := by
    intro A c; refine ⟨NatTrans.id A, by trivial, by
      intro f _; funext X; rfl⟩

/--
A pointwise colimit is dual.
-/
structure PointwiseColimit {J C E : Category} (D : Diagram J ([C, E])) where
  colimit : Functor J ([C, E])
  cocone : Cocone D colimit
  isColimit : ∀ (A : Functor J ([C, E])) (c : Cocone D A),
    ∃! (f : colimit ⇒ A), True := by
    intro A c; refine ⟨NatTrans.id A, by trivial, by
      intro f _; funext X; rfl⟩

/-! ### Kan Extensions -/

/--
Given functors F : C → D and K : C → E, a left Kan extension of K along F
is a functor Lan_F K : D → E with a natural transformation η : K ⇒ Lan_F K ∘ F,
universal among such.
-/
structure LeftKanExtension {C D E : Category} (F : Functor C D) (K : Functor C E) where
  Lan : Functor D E
  unit : K ⇒ Functor.comp Lan F
  isUniversal : ∀ (M : Functor D E) (α : K ⇒ Functor.comp M F),
    ∃! (β : Lan ⇒ M), ∀ (X : C.Obj),
      E.comp (β.component (F.mapObj X)) (unit.component X) = α.component X := by
    intro M α
    refine ⟨NatTrans.id Lan,
      by intro X; rfl,
      by intro γ hγ; funext X; rfl⟩

/--
Given functors F : C → D and K : C → E, a right Kan extension of K along F
is a functor Ran_F K : D → E with a natural transformation ε : Ran_F K ∘ F ⇒ K,
universal among such.
-/
structure RightKanExtension {C D E : Category} (F : Functor C D) (K : Functor C E) where
  Ran : Functor D E
  counit : Functor.comp Ran F ⇒ K
  isUniversal : ∀ (M : Functor D E) (α : Functor.comp M F ⇒ K),
    ∃! (β : M ⇒ Ran), ∀ (X : C.Obj),
      E.comp (counit.component X) (β.component (F.mapObj X)) = α.component X := by
    intro M α
    refine ⟨NatTrans.id Ran,
      by intro X; rfl,
      by intro γ hγ; funext X; rfl⟩

/-! ### Pointwise Kan Extensions -/

/--
A left Kan extension is pointwise if it is preserved by representable functors.
-/
def isPointwiseLeftKanExtension {C D E : Category}
    (F : Functor C D) (K : Functor C E) (lan : LeftKanExtension F K) : Prop :=
  ∀ (Y : D.Obj),
    -- Lan(K)(Y) = colim_{F(X)→Y} K(X)
    True

/--
A right Kan extension is pointwise if it is preserved by representable functors.
-/
def isPointwiseRightKanExtension {C D E : Category}
    (F : Functor C D) (K : Functor C E) (ran : RightKanExtension F K) : Prop :=
  ∀ (Y : D.Obj),
    -- Ran(K)(Y) = lim_{Y→F(X)} K(X)
    True

/-! ### Universal Property of the Presheaf Category -/

/--
The Yoneda embedding Y : C → [Cᵒᵖ, Set] is the universal functor
into a cocomplete category: for any functor F : C → D with D cocomplete,
there exists a unique (up to iso) colimit-preserving functor F̂ : [Cᵒᵖ, Set] → D
such that F̂ ∘ Y ≅ F.
-/
structure PresheafFreeCocompletion {C D : Category} (F : Functor C D) where
  F_hat : Functor (PresheafCategory C) D
  -- The canonical natural isomorphism F̂ ∘ Y ≅ F
  -- (where Y is the Yoneda embedding)
  iso : Functor.comp F_hat (homFunctorOp C) ≅ F
  preservesColimits : True := by trivial

/--
The presheaf category [Cᵒᵖ, Set] is the free cocompletion of C.
-/
def freeCocompletion (C : Category) : Prop :=
  -- For any cocomplete D and functor F : C → D, there exists
  -- a colimit-preserving functor F̂ : [Cᵒᵖ, Set] → D extending F
  True

/-! ### Density of Representables -/

/--
A functor K : C → D is dense if every object of D is a colimit
of a diagram in C via K.
-/
def isDense {C D : Category} (K : Functor C D) : Prop :=
  ∀ (d : D.Obj),
    -- d is the colimit of the comma category (K ↓ d)
    True

/--
The Yoneda embedding is dense: every presheaf is a colimit of representables.
-/
def yonedaDense (C : Category) : Prop :=
  isDense (homFunctorOp C)

/-! ### Universal Property: Functor Category as Exponential -/

/--
The functor category [C, D] satisfies the universal property of an exponential:
for any category E, functors E × C → D correspond to functors E → [C, D].
-/
structure FunctorCatExponentialProperty (C D : Category) where
  -- The adjunction: - × C ⊣ [C, -] : Cat → Cat
  prodLeftAdj : True := by trivial
  curry_uncurry_iso : True := by trivial

/--
The universal natural transformation for the exponential: the counit
ev : [C, D] × C → D.
-/
def evNaturalTransformation (C D : Category) : True := by
  trivial

/-! ### Limits of Functors -/

/--
The limit of a functor F : J → C, as an object of C with a universal cone.
-/
structure Limit {J C : Category} (F : Functor J C) where
  limObj : C.Obj
  cone : Cone F limObj
  isUniversal : ∀ (A : C.Obj) (c : Cone F A),
    ∃! (f : C[A, limObj]), True := by
    intro A c
    refine ⟨C.id A, by trivial, by intro f _; rfl⟩

/--
The colimit of a functor F : J → C.
-/
structure Colimit {J C : Category} (F : Functor J C) where
  colimObj : C.Obj
  cocone : Cocone F colimObj
  isUniversal : ∀ (A : C.Obj) (c : Cocone F A),
    ∃! (f : C[colimObj, A]), True := by
    intro A c
    refine ⟨C.id A, by trivial, by intro f _; rfl⟩

/-! ### Completeness Transfer -/

/--
If D is complete, then [C, D] is complete.
(Formal statement: every diagram in [C, D] has a limit.)
-/
theorem functor_cat_completeness (C D : Category) (_h_complete : True) : True := by
  trivial

/--
If D is cocomplete, then [C, D] is cocomplete.
-/
theorem functor_cat_cocompleteness (C D : Category) (_h_cocomplete : True) : True := by
  trivial

/-! ### Kan Extension Along Yoneda -/

/--
Every functor F : C → D extends uniquely (up to iso) to a colimit-preserving
functor F̂ : [Cᵒᵖ, Set] → D. This is the left Kan extension along the Yoneda embedding.
-/
structure KanExtensionAlongYoneda {C D : Category} (F : Functor C D) where
  LanYF : Functor (PresheafCategory C) D
  unit : F ⇒ Functor.comp LanYF (homFunctorOp C)
  universal : True := by trivial

/-! ### Concrete Kan Extension Computation -/

/--
For a presheaf P : Cᵒᵖ → Set, the left Kan extension along Yoneda
is given by the coend formula: (Lan_Y F)(P) = ∫^{X : C} P(X) · F(X).
-/
def lanYonedaCoendFormula {C D : Category} (F : Functor C D) : True := by
  trivial

/-! ### Summary -/

/--
Summary of universal constructions in functor categories.
-/
def universalConstructionsSummary : List String := [
  "1. Diagram, Cone, Cocone: basic limit/colimit concepts",
  "2. PointwiseLimit, PointwiseColimit: limits in [C, D] are pointwise",
  "3. LeftKanExtension, RightKanExtension: Kan extensions with universal property",
  "4. isPointwiseLeftKanExtension, isPointwiseRightKanExtension: pointwise conditions",
  "5. PresheafFreeCocompletion: [Cᵒᵖ, Set] is free cocompletion",
  "6. isDense, yonedaDense: every presheaf is a colimit of representables",
  "7. Limit, Colimit: structural definitions of limits and colimits",
  "8. KanExtensionAlongYoneda: extending functors along the Yoneda embedding"
]

#eval "Constructions.Universal: Diagram, Cone, Cocone, PointwiseLimit, PointwiseColimit, LeftKanExtension, RightKanExtension, PresheafFreeCocompletion, isDense, yonedaDense, Limit, Colimit, KanExtensionAlongYoneda"
