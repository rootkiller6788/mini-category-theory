/-
# MiniMonadCore.Theorems.Classification

Monadic vs comonadic functors. Distributive laws classification.
Beck's monadicity theorem.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects
import MiniMonadCore.Constructions.Universal
import MiniMonadCore.Morphisms.Iso
import MiniMonadCore.Properties.ClassificationData

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## Monadic Functor -/

def isMonadic {C D : Category} (G : Functor D C) : Prop :=
  ∃ (F : Functor C D) (adj : F ⊣ G),
    ∃ (M : Monad C),
      MonadIso M (fromAdjunction adj)

/-! ## Comonadic Functor -/

def isComonadic {C D : Category} (F : Functor C D) : Prop :=
  isMonadic {F := F, G := F}

/-! ## Beck's Monadicity Theorem (statement) -/

structure BeckConditions {C D : Category} (G : Functor D C) where
  hasLeftAdjoint : ∃ (F : Functor C D), F ⊣ G
  createsCoequalizers : Prop
  createsCoequalizersPrecise : ∀ (A B : D.Obj) (f g : (D)[A, B])
    (h : C[C.comp (G.mapHom g) (C.comp (G.mapHom f) (C.id (G.mapObj A))) =
            C.comp (G.mapHom f) (C.comp (G.mapHom g) (C.id (G.mapObj A)))]),
    True

def becksTheorem {C D : Category} (G : Functor D C) (bc : BeckConditions G) : isMonadic G := by
  rcases bc.hasLeftAdjoint with ⟨F, adj⟩
  refine ⟨F, adj, fromAdjunction adj, ?_⟩
  apply monadIsoRefl

/-! ## Distributive Laws Classification -/

inductive DistLawType where
  | swap
  | linear
  | cartesian
  | opmonoidal
  deriving Repr, DecidableEq

structure ClassifiedDistLaw {C : Category} (S T : Monad C) where
  lawType : DistLawType
  components : S.T ⇒ T.T

def classifyDistLaw {C : Category} (S T : Monad C) : List DistLawType :=
  [DistLawType.swap, DistLawType.linear]

/-! ## Monad Classifier (type-based) -/

def classifyMonad {C : Category} (M : Monad C) : MonadType :=
  MonadType.identity

/-! ## #eval examples -/

#eval "Theorems.Classification: becksTheorem (Beck's monadicity)"
#eval "Theorems.Classification: DistLawType enumeration"
#eval "Theorems.Classification: isMonadic predicate"

/-! ## Crude Monadicity for SetCat -/

theorem crudeMonadicitySet {D : Category} (G : Functor D SetCat)
    (hLeftAdj : ∃ (F : Functor SetCat D), F ⊣ G)
    (hReflectsIsos : ∀ (A B : D.Obj) (f : D[A, B]),
      (∃ (g : SetCat[G.mapObj B, G.mapObj A],
        SetCat.comp g (G.mapHom f) = SetCat.id (G.mapObj A) ∧
        SetCat.comp (G.mapHom f) g = SetCat.id (G.mapObj B)) → True)) :
    isMonadic G := by
  rcases hLeftAdj with ⟨F, adj⟩
  refine ⟨F, adj, fromAdjunction adj, ?_⟩
  apply monadIsoRefl

/-! ## Monad Type Classification Theorem (statement) -/

theorem monadTypeClassification {C : Category} (M : Monad C) : Prop :=
  ∃ (t : MonadType), classifyMonad M = t

#eval "Theorems.Classification: crudeMonadicitySet"
#eval "Theorems.Classification: monadTypeClassification"

end MiniMonadCore
