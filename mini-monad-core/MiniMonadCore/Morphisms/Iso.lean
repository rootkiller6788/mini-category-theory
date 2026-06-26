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

#eval "Morphisms.Iso: monadIsoComp"

end MiniMonadCore
