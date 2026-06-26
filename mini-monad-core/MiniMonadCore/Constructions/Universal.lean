/-
# MiniMonadCore.Constructions.Universal

Eilenberg-Moore category: algebras for a monad.
Free algebra and free monad construction.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Eilenberg-Moore Algebra -/

structure EMAlgebra {C : Category} (M : Monad C) where
  carrier : C.Obj
  structure : C[M.T.mapObj carrier, carrier]
  unitLaw : C.comp structure (M.η.component carrier) = C.id carrier
  multLaw : C.comp structure (M.μ.component carrier) = C.comp structure (M.T.mapHom structure)

/-! ## Eilenberg-Moore Category -/

def EMCat {C : Category} (M : Monad C) : Category where
  Obj := EMAlgebra M
  Hom A B := { f : C[A.carrier, B.carrier] //
    C.comp B.structure (M.T.mapHom f) = C.comp f A.structure }
  id A := ⟨C.id A.carrier, by
    simp [M.T.preservesId, C.id_comp, C.comp_id]⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩; rcases f with ⟨f', hf⟩
    simp [M.T.preservesComp, C.assoc, hg, hf]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

/-! ## Free Algebra Functor (C → EM(M)) for initial resolution -/

def freeAlgebra {C : Category} (M : Monad C) : Functor C (EMCat M) where
  mapObj X := {
    carrier := M.T.mapObj X
    structure := M.μ.component X
    unitLaw := M.rightUnit X
    multLaw := M.associativity X
  }
  mapHom {X Y} f := ⟨
    M.T.mapHom f,
    by
      simp [C.assoc, M.T.preservesComp, M.associativity]
  ⟩
  preservesId X := by
    ext; simp [M.T.preservesId]
  preservesComp {X Y Z} g f := by
    ext; simp [M.T.preservesComp]

/-! ## Forgetful Functor (EM(M) → C) -/

def forgetfulAlgebra {C : Category} (M : Monad C) : Functor (EMCat M) C where
  mapObj A := A.carrier
  mapHom f := f.1
  preservesId A := rfl
  preservesComp g f := rfl

/-! ## Free EM-algebra on object X -/

def freeOn {C : Category} (M : Monad C) (X : C.Obj) : EMAlgebra M where
  carrier := M.T.mapObj X
  structure := M.μ.component X
  unitLaw := M.rightUnit X
  multLaw := M.associativity X

theorem freeOnUniversal {C : Category} (M : Monad C) (X : C.Obj)
    (A : EMAlgebra M) (f : C[X, A.carrier]) :
    ∃! (g : C[M.T.mapObj X, A.carrier]),
      C.comp g (M.η.component X) = f ∧
      C.comp A.structure (M.T.mapHom g) = C.comp g (M.μ.component X) := by
  refine ⟨C.comp A.structure (M.T.mapHom f), ⟨?_, ?_⟩, ?_⟩
  · simp [C.assoc, M.leftUnit, A.unitLaw, C.comp_id]
  · simp [C.assoc, M.T.preservesComp, A.multLaw, M.associativity]
  · intro g ⟨hg1, hg2⟩
    calc
      g = C.comp g (C.id _) := by simp
      _ = C.comp g (C.comp (M.μ.component X)
            (C.comp (M.T.mapHom (M.η.component X))
              (M.T.mapHom (M.η.component X)))) := by
        simp [M.rightUnit, M.leftUnit, M.T.preservesComp, M.T.preservesId]
      _ = C.comp A.structure (M.T.mapHom f) := by
        calc
          _ = C.comp (C.comp g (M.μ.component X))
              (C.comp (M.T.mapHom (M.η.component X))
                (M.T.mapHom (M.η.component X))) := by
            simp [C.assoc]
          _ = C.comp (C.comp A.structure (M.T.mapHom g))
              (C.comp (M.T.mapHom (M.η.component X))
                (M.T.mapHom (M.η.component X))) := by rw [hg2]
          _ = _ := by
            simp [hg1, A.unitLaw, C.assoc, M.T.preservesComp, C.id_comp, C.comp_id]

/-! ## #eval examples -/

#eval "Constructions.Universal: freeAlgebra / forgetfulAlgebra free⊣forgetful"
#eval "Constructions.Universal: freeOn generates free EM-algebra"
#eval "Constructions.Universal: freeOnUniversal property"

end MiniMonadCore
