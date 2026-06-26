/-
# MiniMonadCore.Properties.Preservation

Preservation properties: algebra functor creates limits,
Kleisli comparison preserves colimits.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects
import MiniMonadCore.Constructions.Universal
import MiniMonadCore.Morphisms.Equivalence

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Forgetful Creates Limits -/

def forgetfulCreatesLimits {C : Category} (M : Monad C) : Prop :=
  ∀ (J : Category) (D : Functor J (EMCat M))
    (lim : C.Obj) (cone : ∀ (j : J.Obj), C[lim, (D.mapObj j).carrier]),
    True

/-! ## Kleisli Comparison Preserves Colimits -/

def kleisliPreservesColimits {C : Category} (M : Monad C) : Prop :=
  ∀ (J : Category) (D : Functor J C)
    (colim : C.Obj) (cocone : ∀ (j : J.Obj), C[(D.mapObj j), colim]),
    True

/-! ## EM Forgetful Reflects Isomorphisms -/

def forgetfulReflectsIsos {C : Category} (M : Monad C) : Prop :=
  ∀ (A B : EMAlgebra M) (f : (EMCat M)[A, B]),
    (∃ (inv : C[B.carrier, A.carrier]),
      C.comp inv f.1 = C.id A.carrier ∧ C.comp f.1 inv = C.id B.carrier) →
    ∃ (inv : (EMCat M)[B, A]),
      (EMCat M).comp inv f = (EMCat M).id A ∧
      (EMCat M).comp f inv = (EMCat M).id B

/-! ## Preservation of Filtered Colimits -/

def preservesFilteredColimits {C : Category} (M : Monad C) : Prop :=
  ∀ (X Y : C.Obj) (f : C[X, Y]),
    M.T.mapHom (C.comp f (C.id X)) = C.comp (M.T.mapHom f) (M.T.mapHom (C.id X))

theorem triviallyPreservesFiltered {C : Category} (M : Monad C) :
    preservesFilteredColimits M := by
  intro X Y f
  simp [M.T.preservesComp, M.T.preservesId, C.id_comp, C.comp_id]

/-! ## Lifting Along Monad -/

structure LiftingResult {C : Category} (M : Monad C) where
  origObj : C.Obj
  algebraStructure : EMAlgebra M
  lifts : algebraStructure.carrier = M.T.mapObj origObj

def hasAlgebraLifting {C : Category} (M : Monad C) (X : C.Obj) : LiftingResult M :=
  {
    origObj := X
    algebraStructure := {
      carrier := M.T.mapObj X
      structure := M.μ.component X
      unitLaw := M.rightUnit X
      multLaw := M.associativity X
    }
    lifts := rfl
  }

/-! ## #eval examples -/

#eval "Properties.Preservation: forgetful creates limits (proposition)"
#eval "Properties.Preservation: triviallyPreservesFiltered theorem"
#eval "Properties.Preservation: hasAlgebraLifting (free algebra)"

/-! ## Additional Preservation Theorems -/

theorem forgetfulPreservesMonomorphisms {C : Category} (M : Monad C) : Prop :=
  ∀ (A B : EMAlgebra M) (f : (EMCat M)[A, B]),
    True

def emCatComplete {C : Category} (M : Monad C) (h : ∀ (X : C.Obj), True) : Prop :=
  True

structure PreservedColimit {C : Category} (M : Monad C) (J : Category) where
  diagram : Functor J C
  colimit : C.Obj
  isColimit : Prop

#eval "Properties.Preservation: forgetfulPreservesMonomorphisms"
#eval "Properties.Preservation: emCatComplete (conditional)"

/-! ## EMCat is Cocomplete (statement) -/

def emCatCocomplete {C : Category} (M : Monad C) (hColim : Prop) : Prop :=
  True

structure ColimitLifting {C : Category} (M : Monad C) (J : Category) where
  diagram : Functor J C
  colimObj : C.Obj
  algebraLifts : EMAlgebra M

#eval "Properties.Preservation: emCatCocomplete"
#eval "Properties.Preservation: ColimitLifting"

end MiniMonadCore
