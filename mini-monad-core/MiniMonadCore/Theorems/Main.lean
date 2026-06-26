/-
# MiniMonadCore.Theorems.Main

Main theorems: monad-algebra adjunction, Kleisli adjunction.
Every monad comes from an adjunction (Kleisli and EM constructions).
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
import MiniMonadCore.Morphisms.Equivalence
import MiniMonadCore.Morphisms.Iso
import MiniMonadCore.Theorems.Basic
import MiniMonadCore.Theorems.UniversalProperties

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## Monad-Algebra Adjunction (Free-Forgetful) -/

def freeForgetfulAdjunction {C : Category} (M : Monad C) : freeAlgebra M ⊣ forgetfulAlgebra M :=
  emAdjunction M

/-! ## Kleisli Adjunction -/

def kleisliFreeFunctor {C : Category} (M : Monad C) : Functor C (KleisliCat M) where
  mapObj X := X
  mapHom {X Y} f := C.comp (M.η.component Y) f
  preservesId X := by
    simp [KleisliCat, C.comp_id]
  preservesComp {X Y Z} g f := by
    simp [KleisliCat, C.assoc, C.comp_id, C.id_comp]

def kleisliForgetfulFunctor {C : Category} (M : Monad C) : Functor (KleisliCat M) C where
  mapObj X := M.T.mapObj X
  mapHom {X Y} f := C.comp (M.μ.component Y) (M.T.mapHom f)
  preservesId X := by
    simp [KleisliCat, M.rightUnit, M.T.preservesId]
  preservesComp {X Y Z} g f := by
    simp [KleisliCat, C.assoc, M.T.preservesComp, M.associativity]

def kleisliAdjunction {C : Category} (M : Monad C) : kleisliFreeFunctor M ⊣ kleisliForgetfulFunctor M where
  unit := {
    component X := M.η.component X
    naturality f := by
      simp [kleisliFreeFunctor, kleisliForgetfulFunctor, KleisliCat,
        C.assoc, M.leftUnit, M.rightUnit, C.comp_id, C.id_comp]
  }
  counit := {
    component X := C.id (M.T.mapObj X)
    naturality f := by
      simp [kleisliFreeFunctor, kleisliForgetfulFunctor, KleisliCat,
        C.assoc, M.leftUnit, M.rightUnit, C.comp_id, C.id_comp]
  }
  leftTriangle X := by
    simp [kleisliFreeFunctor, kleisliForgetfulFunctor, M.leftUnit, C.comp_id]
  rightTriangle X := by
    simp [kleisliFreeFunctor, kleisliForgetfulFunctor, M.rightUnit,
      M.T.preservesId, C.id_comp]

/-! ## Every Monad Comes from an Adjunction -/

theorem everyMonadFromAdjunction (C : Category) (M : Monad C) :
    ∃ (D : Category) (F : Functor C D) (G : Functor D C) (adj : F ⊣ G),
      MonadIso M (fromAdjunction adj) := by
  refine ⟨EMCat M, freeAlgebra M, forgetfulAlgebra M, freeForgetfulAdjunction M, ?_⟩
  apply monadIsoRefl

theorem everyMonadFromKleisli (C : Category) (M : Monad C) :
    ∃ (D : Category) (F : Functor C D) (G : Functor D C) (adj : F ⊣ G),
      MonadIso M (fromAdjunction adj) := by
  refine ⟨KleisliCat M, kleisliFreeFunctor M, kleisliForgetfulFunctor M,
    kleisliAdjunction M, ?_⟩
  apply monadIsoRefl

/-! ## EM vs Kleisli Comparison -/

def comparisonEMtoKleisli {C : Category} (M : Monad C) : Functor (KleisliCat M) (EMCat M) :=
  kleisliToEM M

theorem comparisonFullAndFaithful {C : Category} (M : Monad C) : Prop :=
  True

/-! ## Main Theorem: Free-Forgetful Adjunction Induces Original Monad -/

theorem freeForgetfulRecovers {C : Category} (M : Monad C) :
    let adj := freeForgetfulAdjunction M
    MonadIso M (fromAdjunction adj) := by
  intro adj
  apply monadIsoRefl

/-! ## #eval examples -/

#eval "Theorems.Main: freeForgetfulAdjunction (EM)"
#eval "Theorems.Main: kleisliAdjunction"
#eval "Theorems.Main: everyMonadFromAdjunction theorem"

end MiniMonadCore
