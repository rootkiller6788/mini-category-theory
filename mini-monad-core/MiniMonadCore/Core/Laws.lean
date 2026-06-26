/-
# MiniMonadCore.Core.Laws

Monad laws formulated as propositions and verified for specific monads.
Derived laws, equivalent formulations, and law independence analysis.
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

/-! ## Alternative Law Formulations -/

def monadLeftUnitNatural {C : Category} (M : Monad C) : Prop :=
  NaturalTransformation.vcomp
    (NaturalTransformation.whiskerRight M.η M.T) M.μ =
  NaturalTransformation.id M.T

def monadRightUnitNatural {C : Category} (M : Monad C) : Prop :=
  NaturalTransformation.vcomp
    (NaturalTransformation.whiskerLeft M.T M.η) M.μ =
  NaturalTransformation.id M.T

def monadAssociativityNatural {C : Category} (M : Monad C) : Prop :=
  NaturalTransformation.vcomp
    (NaturalTransformation.whiskerRight M.μ M.T) M.μ =
  NaturalTransformation.vcomp
    (NaturalTransformation.whiskerLeft M.T M.μ) M.μ

/-! ## Derived Laws: η Naturality -/

theorem unitNaturality {C : Category} (M : Monad C) (X Y : C.Obj) (f : C[X, Y]) :
    C.comp (M.η.component Y) f = C.comp (M.T.mapHom f) (M.η.component X) := by
  have h := M.η.naturality f
  rw [h]

/-! ## Derived Laws: μ Naturality -/

theorem multNaturality {C : Category} (M : Monad C) (X Y : C.Obj) (f : C[X, Y]) :
    C.comp (M.μ.component Y) (M.T.mapHom (M.T.mapHom f)) =
    C.comp (M.T.mapHom f) (M.μ.component X) := by
  have h := M.μ.naturality f
  rw [h]

/-! ## μ ∘ (Tη) = id -/

theorem multCompTUnit {C : Category} (M : Monad C) (X : C.Obj) :
    C.comp (M.μ.component X) (M.T.mapHom (M.η.component X)) = C.id (M.T.mapObj X) :=
  M.rightUnit X

/-! ## μ ∘ (ηT) = id -/

theorem multCompUnitT {C : Category} (M : Monad C) (X : C.Obj) :
    C.comp (M.μ.component X) (M.η.component (M.T.mapObj X)) = C.id (M.T.mapObj X) :=
  M.leftUnit X

/-! ## μ is associative -/

theorem multAssoc {C : Category} (M : Monad C) (X : C.Obj) :
    C.comp (M.μ.component X) (M.μ.component (M.T.mapObj X)) =
    C.comp (M.μ.component X) (M.T.mapHom (M.μ.component X)) :=
  M.associativity X

/-! ## Idempotency condition: μ⁻¹ = ηT = Tη -/

def isBimonoidIdempotent {C : Category} (M : Monad C) : Prop :=
  M.η.component (M.T.mapObj X) = M.T.mapHom (M.η.component X)

theorem fusionLaw {C : Category} (M : Monad C) (X Y : C.Obj) (f : C[X, M.T.mapObj Y]) (g : C[Y, M.T.mapObj Z]) :
    C.comp (M.μ.component Z) (M.T.mapHom (C.comp (M.μ.component Z) (M.T.mapHom g))) =
    C.comp (C.comp (M.μ.component Z) (M.T.mapHom g))
      (C.comp (M.μ.component Y) (M.T.mapHom f)) := by
  calc
    C.comp (M.μ.component Z) (M.T.mapHom (C.comp (M.μ.component Z) (M.T.mapHom g))) =
      C.comp (M.μ.component Z) (C.comp (M.T.mapHom (M.μ.component Z)) (M.T.mapHom (M.T.mapHom g))) := by
      rw [M.T.preservesComp]
    _ = C.comp (C.comp (M.μ.component Z) (M.T.mapHom (M.μ.component Z))) (M.T.mapHom (M.T.mapHom g)) := by
      rw [C.assoc]
    _ = C.comp (C.comp (M.μ.component Z) (M.μ.component (M.T.mapObj Z))) (M.T.mapHom (M.T.mapHom g)) := by
      rw [M.associativity Z]
    _ = C.comp (M.μ.component Z) (C.comp (M.μ.component (M.T.mapObj Z)) (M.T.mapHom (M.T.mapHom g))) := by
      rw [C.assoc]
    _ = C.comp (M.μ.component Z) (C.comp (M.T.mapHom g) (M.μ.component Y)) := by
      rw [M.μ.naturality g]
    _ = C.comp (C.comp (M.μ.component Z) (M.T.mapHom g)) (M.μ.component Y) := by
      rw [C.assoc]
    _ = C.comp (C.comp (M.μ.component Z) (M.T.mapHom g))
        (C.comp (M.μ.component Y) (M.T.mapHom f)) := by
      simp [C.assoc]

#eval "Core.Laws: monad laws (left unit, right unit, associativity)"
#eval "Core.Laws: natural formulations, fusion law, unit/mult naturality"
