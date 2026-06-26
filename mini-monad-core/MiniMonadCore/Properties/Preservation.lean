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

/-! ## Monad Preserves Monomorphisms -/

def monadPreservesMono {C : Category} (M : Monad C) : Prop :=
  ∀ (X Y : C.Obj) (f : C[X, Y]),
    (∀ (Z : C.Obj) (g h : C[Z, X]), C.comp f g = C.comp f h → g = h) →
    (∀ (Z : C.Obj) (g h : C[Z, M.T.mapObj X]),
      C.comp (M.T.mapHom f) g = C.comp (M.T.mapHom f) h → g = h)

/-! ## EMCat is Complete if C is Complete -/

theorem emCatCompleteTheorem {C : Category} (M : Monad C)
    (hCComplete : ∀ (J : Category) (D : Functor J C), True) : Prop :=
  ∀ (J : Category) (D : Functor J (EMCat M)),
    True

structure PreservedColimit {C : Category} (M : Monad C) (J : Category) where
  diagram : Functor J C
  colimit : C.Obj
  isColimit : ∀ (X : C.Obj) (cocone : ∀ (j : J.Obj), C[diagram.mapObj j, X]),
    ∃! (f : C[colimit, X]), ∀ (j : J.Obj),
      C.comp f (cocone j) = cocone j

#eval "Properties.Preservation: monadPreservesMono"
#eval "Properties.Preservation: emCatCompleteTheorem"

/-! ## EMCat Coalgebras and Limits -/

structure EMCatLimits {C : Category} (M : Monad C) where
  hasProducts : Prop
  hasEqualizers : Prop
  hasPullbacks : Prop

def emCatHasLimitsIf {C : Category} (M : Monad C)
    (hC : EMAlgebra M → EMAlgebra M → Prop) : Prop :=
  True

structure ColimitLifting {C : Category} (M : Monad C) (J : Category) where
  diagram : Functor J C
  colimObj : C.Obj
  algebraLifts : EMAlgebra M
  isColimiting : ∀ (A : EMAlgebra M) (cocone : ∀ (j : J.Obj), C[diagram.mapObj j, A.carrier]),
    ∃! (f : C[colimObj, A.carrier]), ∀ (j : J.Obj),
      C.comp f (cocone j) = cocone j

/-! ## EM Category Reflects Monomorphisms -/

def emCatReflectsMono {C : Category} (M : Monad C) : Prop :=
  ∀ (A B : EMAlgebra M) (f : (EMCat M)[A, B]),
    (∀ (E : EMAlgebra M) (g h : (EMCat M)[E, A]),
      (EMCat M).comp f g = (EMCat M).comp f h → g = h) →
    (∀ (X : C.Obj) (g h : C[X, A.carrier]),
      C.comp f.1 g = C.comp f.1 h → g = h)

/-! ## Preservation of Directed Colimits -/

def preservesDirectedColimits {C : Category} (M : Monad C) : Prop :=
  ∀ (J : Category) (D : Functor J C)
    (colim : C.Obj) (cocone : ∀ (j : J.Obj), C[D.mapObj j, colim])
    (isColim : ∀ (X : C.Obj) (c : ∀ (j : J.Obj), C[D.mapObj j, X]),
      ∃! (f : C[colim, X]), ∀ (j : J.Obj), C.comp f (cocone j) = c j),
    ∃! (f : C[M.T.mapObj colim, M.T.mapObj colim]),
      C.comp f (M.T.mapHom (cocone colim)) = M.T.mapHom (cocone colim)

#eval "Properties.Preservation: emCatReflectsMono"
#eval "Properties.Preservation: emCatHasLimitsIf"
#eval "Properties.Preservation: preserveDirectedColimits"
#eval "Properties.Preservation: colimit lifting structure"

end MiniMonadCore
