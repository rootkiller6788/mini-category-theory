/-
# MiniMonadCore.Morphisms.Iso

Monad isomorphism and algebra isomorphism. Two monads are equivalent
when there exists an invertible monad morphism between them.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Constructions.Universal
import MiniMonadCore.Morphisms.Hom

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad Isomorphism -/

structure MonadIso {C : Category} (M N : Monad C) where
  toMor : MonadMorphism M N
  fromMor : MonadMorphism N M
  leftInv : ∀ (X : C.Obj),
    C.comp (fromMor.component.component X) (toMor.component.component X) = C.id (M.T.mapObj X)
  rightInv : ∀ (X : C.Obj),
    C.comp (toMor.component.component X) (fromMor.component.component X) = C.id (N.T.mapObj X)

def monadIsoRefl {C : Category} (M : Monad C) : MonadIso M M where
  toMor := {
    component := NaturalTransformation.id M.T
    unitCompat := fun X => by simp [C.id_comp]
    multCompat := fun X => by
      simp [NaturalTransformation.id, NaturalTransformation.vcomp, C.id_comp, C.comp_id]
  }
  fromMor := {
    component := NaturalTransformation.id M.T
    unitCompat := fun X => by simp [C.id_comp]
    multCompat := fun X => by
      simp [NaturalTransformation.id, NaturalTransformation.vcomp, C.id_comp, C.comp_id]
  }
  leftInv := fun X => by simp
  rightInv := fun X => by simp

def monadIsoSymm {C : Category} {M N : Monad C} (iso : MonadIso M N) : MonadIso N M where
  toMor := iso.fromMor
  fromMor := iso.toMor
  leftInv := iso.rightInv
  rightInv := iso.leftInv

/-! ## Algebra Isomorphism -/

structure AlgebraIso {C : Category} {M : Monad C} (A B : EMAlgebra M) where
  toHom : AlgebraHom A B
  fromHom : AlgebraHom B A
  leftInv : C.comp fromHom.hom toHom.hom = C.id A.carrier
  rightInv : C.comp toHom.hom fromHom.hom = C.id B.carrier

/-! ## Equivalent Monads -/

def areEquivalentMonads {C : Category} (M N : Monad C) : Prop :=
  Nonempty (MonadIso M N)

theorem equivalentMonadsRefl {C : Category} (M : Monad C) : areEquivalentMonads M M :=
  ⟨monadIsoRefl M⟩

theorem equivalentMonadsSymm {C : Category} {M N : Monad C}
    (h : areEquivalentMonads M N) : areEquivalentMonads N M := by
  rcases h with ⟨iso⟩
  exact ⟨monadIsoSymm iso⟩

/-! ## #eval examples -/

#eval "Morphisms.Iso: MonadIso structure"
#eval "Morphisms.Iso: monadIsoRefl (identity iso)"
#eval "Morphisms.Iso: AlgebraIso for EM-algebras"

/-! ## Composition of Monad Isomorphisms -/

def monadIsoComp {C : Category} {M N P : Monad C}
    (iso1 : MonadIso M N) (iso2 : MonadIso N P) : MonadIso M P where
  toMor := {
    component := NaturalTransformation.vcomp iso2.toMor.component iso1.toMor.component
    unitCompat X := by
      simp [NaturalTransformation.vcomp, C.assoc, iso1.toMor.unitCompat, iso2.toMor.unitCompat]
    multCompat X := by
      simp [NaturalTransformation.vcomp, C.assoc, iso1.toMor.multCompat, iso2.toMor.multCompat]
  }
  fromMor := {
    component := NaturalTransformation.vcomp iso1.fromMor.component iso2.fromMor.component
    unitCompat X := by
      simp [NaturalTransformation.vcomp, C.assoc, iso1.fromMor.unitCompat, iso2.fromMor.unitCompat]
    multCompat X := by
      simp [NaturalTransformation.vcomp, C.assoc, iso1.fromMor.multCompat, iso2.fromMor.multCompat]
  }
  leftInv X := by
    simp [NaturalTransformation.vcomp, C.assoc, iso1.leftInv, iso2.leftInv]
  rightInv X := by
    simp [NaturalTransformation.vcomp, C.assoc, iso1.rightInv, iso2.rightInv]

/-! ## Monad Isomorphism Preserves Structure -/

theorem monadIsoPreservesUnit {C : Category} {M N : Monad C} (iso : MonadIso M N) (X : C.Obj) :
    C.comp (iso.toMor.component.component X) (M.η.component X) = N.η.component X :=
  iso.toMor.unitCompat X

theorem monadIsoPreservesMult {C : Category} {M N : Monad C} (iso : MonadIso M N) (X : C.Obj) :
    C.comp (iso.toMor.component.component X) (M.μ.component X) =
    C.comp (N.μ.component X)
      (NaturalTransformation.vcomp iso.toMor.component iso.toMor.component).component X :=
  iso.toMor.multCompat X

theorem monadIsoFromToId {C : Category} {M N : Monad C} (iso : MonadIso M N) (X : C.Obj) :
    C.comp (iso.fromMor.component.component X) (iso.toMor.component.component X) = C.id (M.T.mapObj X) :=
  iso.leftInv X

theorem monadIsoToFromId {C : Category} {M N : Monad C} (iso : MonadIso M N) (X : C.Obj) :
    C.comp (iso.toMor.component.component X) (iso.fromMor.component.component X) = C.id (N.T.mapObj X) :=
  iso.rightInv X

/-! ## Equivalence of Monads is an Equivalence Relation -/

theorem equivalentMonadsTrans {C : Category} {M N P : Monad C}
    (h1 : areEquivalentMonads M N) (h2 : areEquivalentMonads N P) : areEquivalentMonads M P := by
  rcases h1 with ⟨iso1⟩
  rcases h2 with ⟨iso2⟩
  exact ⟨monadIsoComp iso1 iso2⟩

theorem equivalentMonadsEquivalence {C : Category} :
    Equivalence (areEquivalentMonads (C := C)) where
  refl M := equivalentMonadsRefl M
  symm h := equivalentMonadsSymm h
  trans h1 h2 := equivalentMonadsTrans h1 h2

/-! ## Algebra Isomorphism Properties -/

theorem algebraIsoReversible {C : Category} {M : Monad C} {A B : EMAlgebra M}
    (iso : AlgebraIso A B) :
    C.comp iso.toHom.hom iso.fromHom.hom = C.id B.carrier :=
  iso.rightInv

theorem algebraIsoFromToId {C : Category} {M : Monad C} {A B : EMAlgebra M}
    (iso : AlgebraIso A B) :
    C.comp iso.fromHom.hom iso.toHom.hom = C.id A.carrier :=
  iso.leftInv

/-! ## MonadIso Transport -/

def transportMonadAlongIso {C : Category} {M N : Monad C}
    (iso : MonadIso M N) (A : EMAlgebra M) : EMAlgebra N where
  carrier := A.carrier
  structure := C.comp A.structure (iso.fromMor.component.component A.carrier)
  unitLaw := by
    calc
      C.comp (C.comp A.structure (iso.fromMor.component.component A.carrier))
          (N.η.component A.carrier) =
        C.comp A.structure
          (C.comp (iso.fromMor.component.component A.carrier) (N.η.component A.carrier)) := by
        rw [C.assoc]
      _ = C.comp A.structure (M.η.component A.carrier) := by
        rw [iso.fromMor.unitCompat A.carrier]
      _ = C.id A.carrier := A.unitLaw
  multLaw := by
    calc
      C.comp (C.comp A.structure (iso.fromMor.component.component A.carrier))
          (N.μ.component A.carrier) =
        C.comp A.structure
          (C.comp (iso.fromMor.component.component A.carrier) (N.μ.component A.carrier)) := by
        rw [C.assoc]
      _ = C.comp A.structure
          (C.comp (M.μ.component A.carrier)
            ((NaturalTransformation.vcomp iso.fromMor.component iso.fromMor.component).component A.carrier)) := by
        rw [iso.fromMor.multCompat A.carrier]
      _ = C.comp (C.comp A.structure (M.μ.component A.carrier))
          ((NaturalTransformation.vcomp iso.fromMor.component iso.fromMor.component).component A.carrier) := by
        rw [C.assoc]
      _ = C.comp (C.comp A.structure (M.T.mapHom A.structure))
          ((NaturalTransformation.vcomp iso.fromMor.component iso.fromMor.component).component A.carrier) := by
        rw [A.multLaw]
      _ = C.comp A.structure
          (C.comp (M.T.mapHom A.structure)
            ((NaturalTransformation.vcomp iso.fromMor.component iso.fromMor.component).component A.carrier)) := by
        rw [C.assoc]
      _ = C.comp (C.comp A.structure (iso.fromMor.component.component A.carrier))
          (N.T.mapHom (C.comp A.structure (iso.fromMor.component.component A.carrier))) := by
        simp [C.assoc, N.T.preservesComp]

#eval "Morphisms.Iso: monadIsoComp, transportMonadAlongIso"
#eval "Morphisms.Iso: equivalence relation proofs"
#eval "Morphisms.Iso: algebraIso properties"

end MiniMonadCore
