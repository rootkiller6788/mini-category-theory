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

/-! ## Category of Monads (Mon(C)) -/

def monadCategory (C : Category) : Category where
  Obj := Monad C
  Hom M N := MonadMorphism M N
  id M := monadMorphismId M
  comp ψ φ := monadMorphismComp ψ φ
  comp_id f := by
    ext X; simp [monadMorphismId, monadMorphismComp, NaturalTransformation.vcomp, C.id_comp]
  id_comp f := by
    ext X; simp [monadMorphismId, monadMorphismComp, NaturalTransformation.vcomp, C.comp_id]
  assoc f g h := by
    ext X; simp [monadMorphismComp, NaturalTransformation.vcomp, C.assoc]

/-! ## Monad Morphism from Adjunction -/

def monadMorphismFromAdjunction {C D : Category}
    {F1 F2 : Functor C D} {G1 G2 : Functor D C}
    (adj1 : F1 ⊣ G1) (adj2 : F2 ⊣ G2)
    (α : F1 ⇒ F2) : MonadMorphism (fromAdjunction adj1) (fromAdjunction adj2) where
  component := NaturalTransformation.vcomp
    (NaturalTransformation.whiskerRight α G2)
    (NaturalTransformation.whiskerLeft G2 (NaturalTransformation.id F2))
  unitCompat X := by
    simp [fromAdjunction, C.assoc, adj1.leftTriangle, adj2.leftTriangle]
  multCompat X := by
    simp [fromAdjunction, C.assoc, D.assoc]

/-! ## Algebra Hom Category -/

def algebraHomCategory {C : Category} (M : Monad C) : Category where
  Obj := EMAlgebra M
  Hom A B := AlgebraHom A B
  id A := algebraHomId A
  comp g f := algebraHomComp g f
  comp_id f := by
    ext; simp [algebraHomId, algebraHomComp, C.comp_id]
  id_comp f := by
    ext; simp [algebraHomId, algebraHomComp, C.id_comp]
  assoc f g h := by
    ext; simp [algebraHomComp, C.assoc]

/-! ## Morphism Composition Laws -/

theorem monadMorphismCompAssoc {C : Category} {M N P Q : Monad C}
    (φ : MonadMorphism P Q) (ψ : MonadMorphism N P) (χ : MonadMorphism M N)
    (X : C.Obj) :
    C.comp ((monadMorphismComp φ (monadMorphismComp ψ χ)).component.component X) (C.id X) =
    C.comp ((monadMorphismComp (monadMorphismComp φ ψ) χ).component.component X) (C.id X) := by
  simp [monadMorphismComp, NaturalTransformation.vcomp, C.assoc, C.comp_id]

theorem monadMorphismIdentityLeft {C : Category} {M N : Monad C}
    (φ : MonadMorphism M N) (X : C.Obj) :
    C.comp ((monadMorphismComp (monadMorphismId N) φ).component.component X) (C.id (M.T.mapObj X)) =
    φ.component.component X := by
  simp [monadMorphismComp, monadMorphismId, NaturalTransformation.vcomp, C.id_comp, C.comp_id]

theorem monadMorphismIdentityRight {C : Category} {M N : Monad C}
    (φ : MonadMorphism M N) (X : C.Obj) :
    C.comp ((monadMorphismComp φ (monadMorphismId M)).component.component X) (C.id (M.T.mapObj X)) =
    φ.component.component X := by
  simp [monadMorphismComp, monadMorphismId, NaturalTransformation.vcomp, C.id_comp, C.comp_id]

#eval "Morphisms.Hom: monadMorphismId"
#eval "Morphisms.Hom: monadMorphismComp"
#eval "Morphisms.Hom: monadCategory, algebraHomCategory"
#eval "Morphisms.Hom: monadMorphismFromAdjunction"

end MiniMonadCore
