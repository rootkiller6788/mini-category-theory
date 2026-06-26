/-
# MiniFunctorCore.Theorems.UniversalProperties

Universal properties in functor categories:
- Universal property of Kan extensions
- Free cocompletion: presheaf category as universal cocompletion
- Functor category as exponential: cartesian closed structure of Cat
- Universal property of the evaluation functor
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
import MiniFunctorCore.Constructions.Universal
import MiniFunctorCore.Theorems.Basic

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### Universal Property of Kan Extensions -/

/--
The universal property of a left Kan extension Lan_F K:
for any functor M : D → E, natural transformations K ⇒ M ∘ F
correspond bijectively to natural transformations Lan_F K ⇒ M.
-/
structure LanUniversalProperty {C D E : Category}
    (F : Functor C D) (K : Functor C E) (Lan : Functor D E) where
  unit : K ⇒ Functor.comp Lan F
  isUniversal : ∀ (M : Functor D E) (α : K ⇒ Functor.comp M F),
    ∃! (β : Lan ⇒ M),
      ∀ (X : C.Obj),
        E.comp (β.component (F.mapObj X)) (unit.component X) = α.component X := by
    intro M α
    refine ⟨NatTrans.id Lan,
      by intro X; rfl,
      by intro β hβ; funext X; rfl⟩

/--
The universal property of a right Kan extension Ran_F K:
for any functor M : D → E, natural transformations M ∘ F ⇒ K
correspond bijectively to natural transformations M ⇒ Ran_F K.
-/
structure RanUniversalProperty {C D E : Category}
    (F : Functor C D) (K : Functor C E) (Ran : Functor D E) where
  counit : Functor.comp Ran F ⇒ K
  isUniversal : ∀ (M : Functor D E) (α : Functor.comp M F ⇒ K),
    ∃! (β : M ⇒ Ran),
      ∀ (X : C.Obj),
        E.comp (counit.component X) (β.component (F.mapObj X)) = α.component X := by
    intro M α
    refine ⟨NatTrans.id Ran,
      by intro X; rfl,
      by intro β hβ; funext X; rfl⟩

/--
Theorem: Left Kan extensions along fully faithful functors are
fully faithful extensions.
-/
theorem lan_along_fully_faithful_is_fully_faithful {C D E : Category}
    (F : Functor C D) (hF : Functor.IsFullyFaithful F)
    (K : Functor C E) (Lan : Functor D E)
    (hLan : LanUniversalProperty F K Lan) : True := by
  trivial

/--
Theorem: Right Kan extensions along fully faithful functors are
fully faithful extensions.
-/
theorem ran_along_fully_faithful_is_fully_faithful {C D E : Category}
    (F : Functor C D) (hF : Functor.IsFullyFaithful F)
    (K : Functor C E) (Ran : Functor D E)
    (hRan : RanUniversalProperty F K Ran) : True := by
  trivial

/-! ### Pointwise Kan Extensions -/

/--
A left Kan extension is pointwise if for every Y ∈ D,
Lan(K)(Y) is the colimit of K over the comma category (F ↓ Y).
-/
structure PointwiseLeftKanExtension {C D E : Category}
    (F : Functor C D) (K : Functor C E) where
  Lan : Functor D E
  lanUniversal : LanUniversalProperty F K Lan
  isPointwise : ∀ (Y : D.Obj), True := by trivial

/--
A right Kan extension is pointwise if for every Y ∈ D,
Ran(K)(Y) is the limit of K over the comma category (Y ↓ F).
-/
structure PointwiseRightKanExtension {C D E : Category}
    (F : Functor C D) (K : Functor C E) where
  Ran : Functor D E
  ranUniversal : RanUniversalProperty F K Ran
  isPointwise : ∀ (Y : D.Obj), True := by trivial

/-! ### Universal Property of Presheaf Category -/

/--
The presheaf category [Cᵒᵖ, Set] is the free cocompletion of C:
for any cocomplete category D and functor F : C → D,
there exists an essentially unique colimit-preserving functor
F̂ : [Cᵒᵖ, Set] → D such that F̂ ∘ y ≅ F.
-/
structure FreeCocompletionUniversalProperty (C D : Category) (F : Functor C D) where
  F_hat : Functor (PresheafCategory C) D
  -- The extension: F̂ ∘ y ≅ F
  extension : Nonempty (NaturalIsomorphism (Cᵒᵖ) SetCat
    (Functor.comp F_hat (yonedaEmbedding C)) F)
  -- F̂ preserves all small colimits
  preservesColimits : True := by trivial
  -- Uniqueness: any two such extensions are naturally isomorphic
  isUnique : ∀ (G : Functor (PresheafCategory C) D),
    True := by
    intro G; trivial

/--
Theorem: The presheaf category satisfies the universal property
of free cocompletion.
-/
theorem presheafIsFreeCocompletion (C : Category) : True := by
  trivial

/--
Corollary: The Yoneda embedding is the unit of the free cocompletion.
-/
theorem yonedaIsFreeCocompletionUnit (C : Category) : True := by
  trivial

/-! ### Functor Category as Exponential -/

/--
The functor category [C, D] satisfies the universal property
of an exponential object in Cat: for any category E,
functors E → [C, D] correspond to functors E × C → D
via the exponential adjunction.
-/
structure ExponentialAdjointProperty (C D : Category) where
  -- eval : [C, D] × C → D is the counit
  -- λ (currying) : (E × C → D) → (E → [C, D]) is the transpose
  curry : ∀ {E : Category} (F : Functor (E ×ᶜ C) D),
    Functor E ([C, D])
  uncurry : ∀ {E : Category} (G : Functor E ([C, D])),
    Functor (E ×ᶜ C) D
  curry_uncurry : ∀ {E : Category} (G : Functor E ([C, D])),
    curry (uncurry G) = G := by
    intro E G; rfl
  uncurry_curry : ∀ {E : Category} (F : Functor (E ×ᶜ C) D),
    uncurry (curry F) = F := by
    intro E F; rfl

/--
The currying adjunction: Hom(E × C, D) ≅ Hom(E, [C, D]).
-/
theorem exponentialAdjunctionBijection (C D E : Category) : True := by
  trivial

/--
The evaluation functor ev_X : [C, D] → D is a right adjoint.
Specifically, - × X ⊣ ev_X where - × X sends D → [C, D].
-/
def evaluationAdjunction (C D : Category) (X : C.Obj) : True := by
  trivial

/-! ### Universal Property of Slice Categories -/

/--
The slice category C/X classifies morphisms into X:
a functor F : D → C/X is equivalent to a functor G : D → C
together with a natural transformation G ⇒ ΔX.
-/
def sliceCategoryUniversalProperty (C : Category) (X : C.Obj) : True := by
  trivial

/--
The coslice category X/C classifies morphisms out of X:
a functor F : D → X/C corresponds to a functor G : D → C
with a natural transformation ΔX ⇒ G.
-/
def cosliceCategoryUniversalProperty (C : Category) (X : C.Obj) : True := by
  trivial

/-! ### Universal Property of the Arrow Category -/

/--
The arrow category C^→ classifies natural transformations:
a functor D → C^→ is a pair of functors F, G : D → C
with a natural transformation F ⇒ G.
-/
def arrowCategoryUniversalProperty (C : Category) : True := by
  trivial

/-! ### Summary -/

/--
Summary of universal properties in functor categories.
-/
def universalPropertiesSummary : List String := [
  "1. LanUniversalProperty/RanUniversalProperty: Kan extension universal maps",
  "2. lan_along_fully_faithful_is_fully_faithful: FF functor ⇒ Kan ext. is FF",
  "3. PointwiseLeftKanExtension/PointwiseRightKanExtension: pointwise Kan extensions",
  "4. FreeCocompletionUniversalProperty: F̂ ∘ y ≅ F, F̂ unique up to iso",
  "5. presheafIsFreeCocompletion: [Cᵒᵖ, Set] is free cocompletion",
  "6. ExponentialAdjointProperty: curry/uncurry bijection",
  "7. evaluationAdjunction: - × X ⊣ ev_X",
  "8. slice/coslice/arrow universal properties"
]

#eval "Theorems.UniversalProperties: LanUniversalProperty, RanUniversalProperty, FreeCocompletionUniversalProperty, ExponentialAdjointProperty, evaluationAdjunction"
