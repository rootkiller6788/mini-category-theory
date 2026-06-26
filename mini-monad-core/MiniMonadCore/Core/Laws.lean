/-
# MiniMonadCore.Core.Laws

Monad laws formulated as propositions and verified for specific monads.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Monad Law Propositions -/

def monadLeftUnitLaw {C : Category} (M : Monad C) : Prop :=
  ∀ (X : C.Obj), C.comp (M.μ.component X) (M.η.component (M.T.mapObj X)) = C.id (M.T.mapObj X)

def monadRightUnitLaw {C : Category} (M : Monad C) : Prop :=
  ∀ (X : C.Obj), C.comp (M.μ.component X) (M.T.mapHom (M.η.component X)) = C.id (M.T.mapObj X)

def monadAssociativityLaw {C : Category} (M : Monad C) : Prop :=
  ∀ (X : C.Obj), C.comp (M.μ.component X) (M.μ.component (M.T.mapObj X)) =
    C.comp (M.μ.component X) (M.T.mapHom (M.μ.component X))

theorem monadLawsHold {C : Category} (M : Monad C) :
    monadLeftUnitLaw M ∧ monadRightUnitLaw M ∧ monadAssociativityLaw M := by
  refine ⟨?_, ?_, ?_⟩
  · exact M.leftUnit
  · exact M.rightUnit
  · exact M.associativity

#eval "Core.Laws: monad laws (left unit, right unit, associativity)"
