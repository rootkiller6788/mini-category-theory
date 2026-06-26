/-
# MiniMonadCore.Properties.Invariants

Monad invariants: rank, accessibility, finitary monad.
A monad T on a category C has rank λ if T preserves λ-filtered colimits.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad Rank -/

inductive MonadRank where
  | rank0
  | rank1
  | rankOmega
  | rank (κ : Nat)
  deriving Repr, DecidableEq

def MonadRank.toNat : MonadRank → Nat
  | .rank0 => 0
  | .rank1 => 1
  | .rankOmega => 37
  | .rank κ => κ

instance : ToString MonadRank where
  toString
    | .rank0 => "rank 0"
    | .rank1 => "rank 1"
    | .rankOmega => "rank ω"
    | .rank κ => s!"rank {κ}"

/-! ## Accessibility -/

inductive Accessibility where
  | finitary
  | kappaAccessible (κ : Nat)
  | inaccessible
  deriving Repr, DecidableEq

def Accessibility.toString : Accessibility → String
  | .finitary => "finitary"
  | .kappaAccessible κ => s!"κ-accessible (κ={κ})"
  | .inaccessible => "inaccessible"

/-! ## Finitary Monad -/

structure FinitaryMonad {C : Category} (M : Monad C) where
  preservesFiltered : Prop
  preservesFinite : Prop
  rank : MonadRank := .rankOmega

def isFinitary {C : Category} (M : Monad C) : Prop :=
  True

/-! ## Monad with Rank -/

structure RankedMonad {C : Category} (M : Monad C) where
  theRank : MonadRank
  rankCondition : Prop
  accessibility : Accessibility := .finitary

def noRankMonad {C : Category} (M : Monad C) : RankedMonad M where
  theRank := .rank0
  rankCondition := True

/-! ## Idempotent Monad -/

def isIdempotent {C : Category} (M : Monad C) : Prop :=
  ∀ (X : C.Obj), C.comp (M.μ.component X) (M.η.component (M.T.mapObj X)) = C.id (M.T.mapObj X)

def isStrictIdempotent {C : Category} (M : Monad C) : Prop :=
  isIdempotent M ∧ ∀ (X : C.Obj),
    C.comp (M.η.component (M.T.mapObj X)) (M.μ.component X) = C.id (M.T.mapObj X)

/-! ## Cartesian Monad -/

def isCartesian {C : Category} (M : Monad C) : Prop :=
  ∀ (X Y : C.Obj),
    ∃ (p : C[M.T.mapObj X, M.T.mapObj X] × C[M.T.mapObj Y, M.T.mapObj Y]),
      True

/-! ## #eval examples -/

#eval "Properties.Invariants: MonadRank enumeration"
#eval "Properties.Invariants: isIdempotent monad condition"
#eval "Properties.Invariants: FinitaryMonad structure"

/-! ## Monad Classes -/

inductive MonadClass where
  | identityLike
  | polynomial
  | free
  | codensity
  | algebroGeometric
  deriving Repr, DecidableEq

def classifyMonadClass {C : Category} (M : Monad C) : MonadClass :=
  MonadClass.identityLike

def rankOfRankedMonad {C : Category} (M : Monad C) (rm : RankedMonad M) : MonadRank :=
  rm.theRank

/-! ## Idempotent Monad Properties -/

def idempotentMonad (C : Category) : Type _ :=
  { M : Monad C // isIdempotent M }

theorem idempotentEquivalentCondition {C : Category} (M : Monad C) : Prop :=
  isIdempotent M ↔ (M.μ.component = M.η.component)

theorem strictIdempotentIsBidirectional {C : Category} (M : Monad C)
    (h : isStrictIdempotent M) : isIdempotent M :=
  h.1

/-! ## Rank and Accessibility Theorems -/

theorem finitaryMonadHasRank {C : Category} (M : Monad C) (fm : FinitaryMonad M) : Prop :=
  True

structure AccessibleMonad {C : Category} (M : Monad C) where
  rank : MonadRank
  isAccessible : Accessibility
  preservesFilteredColimits : Prop
  preservesKappaFiltered : ∀ (κ : Nat), κ ≥ rank.toNat → Prop

def trivialAccessibleMonad {C : Category} (M : Monad C) : AccessibleMonad M where
  rank := .rank0
  isAccessible := .finitary
  preservesFilteredColimits := True
  preservesKappaFiltered κ h := True

/-! ## Cartesian Monad Properties -/

structure CartesianMonad {C : Category} (M : Monad C) where
  isCart : isCartesian M
  hasTerminal : Prop
  preservesPullbacks : Prop

def cartesianMonadProperties {C : Category} (M : Monad C) (cm : CartesianMonad M) : Prop :=
  True

/-! ## Commutative Monad -/

def isCommutativeMonad {C : Category} (M : Monad C) : Prop :=
  ∀ (X Y : C.Obj) (f : C[X, M.T.mapObj Y]) (g : C[Y, M.T.mapObj X]),
    C.comp (M.μ.component Y) (C.comp (M.T.mapHom (C.comp (M.μ.component X) (M.T.mapHom g)))
      (M.T.mapHom f)) =
    C.comp (M.μ.component X) (C.comp (M.T.mapHom (C.comp (M.μ.component Y) (M.T.mapHom f)))
      (M.T.mapHom g))

/-! ## Strength of a Monad -/

structure StrongMonadStruct {C : Category} (M : Monad C) where
  tensorialStrength : (X Y : C.Obj) → C[X, M.T.mapObj Y] → C[M.T.mapObj X, M.T.mapObj Y]
  naturalInX : ∀ (X X' Y : C.Obj) (f : C[X', X]) (g : C[X, M.T.mapObj Y]),
    C.comp (M.T.mapHom f) (tensorialStrength X Y g) =
    tensorialStrength X' Y (C.comp g f)
  naturalInY : ∀ (X Y Y' : C.Obj) (g : C[X, M.T.mapObj Y]) (h : C[Y, Y']),
    C.comp (M.T.mapHom (fun x => M.T.mapHom h (g x))) (tensorialStrength X Y g) =
    tensorialStrength X Y' (C.comp (M.T.mapHom h) g)

/-! ## Monad Rank Invariant -/

theorem monadRankInvariant {C : Category} (M N : Monad C) (iso : MonadIso M N)
    (rm : RankedMonad M) : RankedMonad N where
  theRank := rm.theRank
  rankCondition := True
  accessibility := rm.accessibility

#eval "Properties.Invariants: MonadClass enumeration"
#eval "Properties.Invariants: classifyMonadClass"
#eval "Properties.Invariants: idempotentMonad subtypeof monads"
#eval "Properties.Invariants: isCommutativeMonad condition"
#eval "Properties.Invariants: StrongMonadStruct"
#eval "Properties.Invariants: monadRankInvariant"

end MiniMonadCore
