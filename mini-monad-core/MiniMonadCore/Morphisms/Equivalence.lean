/-
# MiniMonadCore.Morphisms.Equivalence

Eilenberg-Moore comparison functor and Kleisli comparison functor.
The free-forgetful adjunction induces the EM and Kleisli resolutions.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects
import MiniMonadCore.Constructions.Universal

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Comparison Functor (Kleisli → EM) -/

def kleisliToEM {C : Category} (M : Monad C) : Functor (KleisliCat M) (EMCat M) where
  mapObj X := {
    carrier := M.T.mapObj X
    structure := M.μ.component X
    unitLaw := M.rightUnit X
    multLaw := by
      calc
        C.comp (M.μ.component X) (M.μ.component (M.T.mapObj X)) =
          C.comp (M.μ.component X) (M.T.mapHom (M.μ.component X)) :=
          M.associativity X
  }
  mapHom {X Y} f := ⟨
    C.comp (M.μ.component Y) (M.T.mapHom f),
    by
      calc
        C.comp (M.μ.component Y) (M.T.mapHom (C.comp (M.μ.component Y) (M.T.mapHom f))) =
          C.comp (M.μ.component Y) (C.comp (M.T.mapHom (M.μ.component Y))
            (M.T.mapHom (M.T.mapHom f))) := by
          rw [M.T.preservesComp]
        _ = C.comp (C.comp (M.μ.component Y) (M.T.mapHom (M.μ.component Y)))
            (M.T.mapHom (M.T.mapHom f)) := by rw [C.assoc]
        _ = C.comp (C.comp (M.μ.component Y) (M.μ.component (M.T.mapObj Y)))
            (M.T.mapHom (M.T.mapHom f)) := by rw [M.associativity Y]
        _ = C.comp (M.μ.component Y)
            (C.comp (M.μ.component (M.T.mapObj Y)) (M.T.mapHom (M.T.mapHom f))) := by
          rw [C.assoc]
        _ = C.comp (C.comp (M.μ.component Y) (M.T.mapHom f)) (M.μ.component X) := by
          simp [C.assoc, M.associativity]
  ⟩
  preservesId X := by
    ext; simp [KleisliCat, C.id_comp, M.rightUnit, M.T.preservesId]
  preservesComp {X Y Z} g f := by
    ext; simp [KleisliCat, C.assoc, M.T.preservesComp, M.associativity]

/-! ## EM Forgetful Functor (alias) -/

abbrev emForgetful {C : Category} (M : Monad C) : Functor (EMCat M) C :=
  forgetfulAlgebra M

/-! ## Free Algebra Functor (alias) -/

abbrev emFree {C : Category} (M : Monad C) : Functor C (EMCat M) :=
  freeAlgebra M

/-! ## Eilenberg-Moore Adjunction -/

def emAdjunction {C : Category} (M : Monad C) : emFree M ⊣ emForgetful M := by
  refine {
    unit := {
      component := fun X => M.η.component X
      naturality := fun f => by
        simp [freeAlgebra, C.assoc, M.leftUnit, M.rightUnit, C.comp_id, C.id_comp]
    }
    counit := {
      component := fun A => A.structure
      naturality := fun {A B} f => by
        rcases f with ⟨f', hf⟩
        simp [hf]
    }
    leftTriangle := fun X => by
      simp [freeAlgebra, forgetfulAlgebra, M.leftUnit]
    rightTriangle := fun A => by
      simp [forgetfulAlgebra, freeAlgebra, M.T.preservesId, A.unitLaw]
  }

/-! ## #eval examples -/

#eval "Morphisms.Equivalence: kleisliToEM comparison functor"
#eval "Morphisms.Equivalence: emAdjunction = free ⊣ forgetful"
#eval "Morphisms.Equivalence: Uses freeAlgebra/forgetfulAlgebra from Constructions.Universal"

end MiniMonadCore
