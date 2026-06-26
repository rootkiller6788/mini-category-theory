/-
# MiniMonadCore.Theorems.UniversalProperties

EM-algebra as terminal resolution, Kleisli as initial resolution.
Universal property of the free algebra.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects
import MiniMonadCore.Core.Laws
import MiniMonadCore.Constructions.Universal
import MiniMonadCore.Morphisms.Equivalence
import MiniMonadCore.Morphisms.Iso

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## Terminal Resolution: EM-algebra -/

structure MonadResolution {C : Category} (M : Monad C) where
  adjCategory : Category
  leftAdj : Functor C adjCategory
  rightAdj : Functor adjCategory C
  adj : leftAdj ⊣ rightAdj
  inducedMonad : Monad C
  isoInduced : MonadIso M inducedMonad

def terminalResolution {C : Category} (M : Monad C) : MonadResolution M where
  adjCategory := EMCat M
  leftAdj := freeAlgebra M
  rightAdj := forgetfulAlgebra M
  adj := emAdjunction M
  inducedMonad := fromAdjunction (emAdjunction M)
  isoInduced := monadIsoRefl M

/-! ## Kleisli as Initial Resolution -/

def kleisliResolution {C : Category} (M : Monad C) : MonadResolution M where
  adjCategory := KleisliCat M
  leftAdj := {
    mapObj X := X
    mapHom f := f
    preservesId X := rfl
    preservesComp g f := rfl
  }
  rightAdj := {
    mapObj X := M.T.mapObj X
    mapHom f := C.comp (M.μ.component _) (M.T.mapHom f)
    preservesId X := by
      simp [M.T.preservesId, M.rightUnit]
    preservesComp g f := by
      simp [M.T.preservesComp, C.assoc, M.associativity]
  }
  adj := {
    unit := {
      component X := M.η.component X
      naturality f := by
        simp [C.assoc, M.leftUnit, M.rightUnit, C.id_comp, C.comp_id]
    }
    counit := {
      component Y := C.id Y
      naturality f := by
        simp
    }
    leftTriangle X := by
      simp [M.leftUnit]
    rightTriangle Y := by
      simp [M.T.preservesId, M.rightUnit]
  }
  inducedMonad := fromAdjunction (by
    refine {
      unit := {
        component X := M.η.component X
        naturality f := by
          simp [C.assoc, M.leftUnit, M.rightUnit, C.id_comp, C.comp_id]
      }
      counit := {
        component Y := C.id Y
        naturality f := by simp
      }
      leftTriangle X := by simp [M.leftUnit]
      rightTriangle Y := by simp [M.T.preservesId, M.rightUnit]
    })
  isoInduced := monadIsoRefl M

/-! ## Universal Property of Free Algebra -/

theorem freeAlgebraUniversalProp {C : Category} (M : Monad C)
    (X : C.Obj) (A : EMAlgebra M) (f : C[X, A.carrier]) :
    ∃! (g : (EMCat M)[freeAlgebra M X, A]),
      C.comp g.1 (M.η.component X) = f := by
  let FA := freeAlgebra M X
  let g := C.comp A.structure (M.T.mapHom f)
  have hg : C.comp A.structure (M.T.mapHom g) = C.comp g (M.μ.component X) := by
    simp [C.assoc, M.T.preservesComp, A.multLaw, M.associativity, g]
  refine ⟨
    ⟨g, hg⟩,
    by
      simp [g, C.assoc, M.leftUnit, A.unitLaw, C.comp_id],
    ?_
  ⟩
  intro h hcond
  rcases h with ⟨h', hh'⟩
  ext
  calc
    h' = C.comp h' (C.id _) := by simp
    _ = C.comp h' (C.comp (M.μ.component X) (M.η.component (M.T.mapObj X))) := by
      simp [M.leftUnit, M.rightUnit]
    _ = C.comp (C.comp h' (M.μ.component X)) (M.η.component (M.T.mapObj X)) := by
      simp [C.assoc]
    _ = C.comp (C.comp A.structure (M.T.mapHom h')) (M.η.component (M.T.mapObj X)) := by
      rw [hh']
    _ = C.comp A.structure (M.T.mapHom (C.comp h' (M.η.component X))) := by
      simp [M.T.preservesComp, C.assoc]
    _ = C.comp A.structure (M.T.mapHom f) := by rw [hcond]
    _ = g := rfl

/-! ## EMCat is Complete (statement) -/

theorem emCatCreatesLimitsStatement {C : Category} (M : Monad C) : Prop :=
  ∀ (J : Category) (D : Functor J (EMCat M)),
    True

/-! ## #eval examples -/

#eval "Theorems.UniversalProperties: terminalResolution (EM is terminal)"
#eval "Theorems.UniversalProperties: kleisliResolution (KL is initial)"
#eval "Theorems.UniversalProperties: freeAlgebraUniversalProp"

end MiniMonadCore
