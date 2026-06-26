/-
# MiniMonadCore.Morphisms.Hom

Monad morphisms: natural transformations compatible with η and μ.
Algebra homomorphisms. Kleisli morphisms as structure.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Constructions.Universal

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad Morphism Properties -/

def preservesUnit {C : Category} {M N : Monad C} (α : M.T ⇒ N.T) : Prop :=
  ∀ (X : C.Obj), C.comp (α.component X) (M.η.component X) = N.η.component X

def preservesMultiplication {C : Category} {M N : Monad C} (α : M.T ⇒ N.T) : Prop :=
  ∀ (X : C.Obj),
    C.comp (α.component X) (M.μ.component X) =
    C.comp (N.μ.component X) (NaturalTransformation.vcomp α α).component X

theorem monadMorphismLaws {C : Category} {M N : Monad C} (φ : MonadMorphism M N) :
    preservesUnit φ.component ∧ preservesMultiplication φ.component := by
  refine ⟨?_, ?_⟩
  · exact φ.unitCompat
  · exact φ.multCompat

/-! ## Algebra Homomorphisms -/

structure AlgebraHom {C : Category} {M : Monad C} (A B : EMAlgebra M) where
  hom : C[A.carrier, B.carrier]
  commutes : C.comp B.structure (M.T.mapHom hom) = C.comp hom A.structure

def algebraHomId {C : Category} {M : Monad C} (A : EMAlgebra M) : AlgebraHom A A where
  hom := C.id A.carrier
  commutes := by
    simp [M.T.preservesId, C.id_comp, C.comp_id]

def algebraHomComp {C : Category} {M : Monad C} {A B D : EMAlgebra M}
    (g : AlgebraHom B D) (f : AlgebraHom A B) : AlgebraHom A D where
  hom := C.comp g.hom f.hom
  commutes := by
    calc
      C.comp D.structure (M.T.mapHom (C.comp g.hom f.hom)) =
        C.comp D.structure (C.comp (M.T.mapHom g.hom) (M.T.mapHom f.hom)) := by
          rw [M.T.preservesComp]
      _ = C.comp (C.comp D.structure (M.T.mapHom g.hom)) (M.T.mapHom f.hom) := by
          rw [C.assoc]
      _ = C.comp (C.comp g.hom B.structure) (M.T.mapHom f.hom) := by rw [g.commutes]
      _ = C.comp g.hom (C.comp B.structure (M.T.mapHom f.hom)) := by rw [C.assoc]
      _ = C.comp g.hom (C.comp f.hom A.structure) := by rw [f.commutes]
      _ = C.comp (C.comp g.hom f.hom) A.structure := by rw [C.assoc]

/-! ## Kleisli Morphisms as Structures -/

structure KleisliHom {C : Category} (M : Monad C) (X Y : C.Obj) where
  k : C[X, M.T.mapObj Y]

def kleisliId {C : Category} (M : Monad C) (X : C.Obj) : KleisliHom M X X where
  k := M.η.component X

def kleisliComp {C : Category} (M : Monad C) {X Y Z : C.Obj}
    (g : KleisliHom M Y Z) (f : KleisliHom M X Y) : KleisliHom M X Z where
  k := C.comp (M.μ.component Z)
    (C.comp (M.T.mapHom g.k) f.k)

theorem kleisliCompAssoc {C : Category} (M : Monad C) {W X Y Z : C.Obj}
    (f : KleisliHom M W X) (g : KleisliHom M X Y) (h : KleisliHom M Y Z) :
    kleisliComp M (kleisliComp M h g) f = kleisliComp M h (kleisliComp M g f) := by
  ext; simp [kleisliComp, C.assoc, M.associativity, M.T.preservesComp]

/-! ## #eval examples -/

#eval "Morphisms.Hom: MonadMorphism laws"
#eval "Morphisms.Hom: AlgebraHom structure"
#eval "Morphisms.Hom: KleisliHom composition"

/-! ## Identity Monad Morphism -/

def monadMorphismId {C : Category} (M : Monad C) : MonadMorphism M M where
  component := NaturalTransformation.id M.T
  unitCompat X := by simp [C.id_comp]
  multCompat X := by
    simp [NaturalTransformation.id, NaturalTransformation.vcomp, C.id_comp, C.comp_id]

/-! ## Composition of Monad Morphisms -/

def monadMorphismComp {C : Category} {M N P : Monad C}
    (ψ : MonadMorphism N P) (φ : MonadMorphism M N) : MonadMorphism M P where
  component := NaturalTransformation.vcomp ψ.component φ.component
  unitCompat X := by
    simp [NaturalTransformation.vcomp, C.assoc, ψ.unitCompat, φ.unitCompat]
  multCompat X := by
    simp [NaturalTransformation.vcomp, C.assoc, ψ.multCompat, φ.multCompat]

#eval "Morphisms.Hom: monadMorphismId"
#eval "Morphisms.Hom: monadMorphismComp"

end MiniMonadCore
