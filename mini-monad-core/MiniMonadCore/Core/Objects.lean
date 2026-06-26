/-
# MiniMonadCore.Core.Objects

Kleisli category: given a monad M on C, the Kleisli category Kl(M)
has objects of C and morphisms Kl_M(X, Y) = C[X, M.T(Y)].

Also: coKleisli category, EM-category shell, monad object in a 2-category.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniNaturalTransformation.Core.Basic
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Kleisli Category -/

def KleisliCat {C : Category} (M : Monad C) : Category where
  Obj := C.Obj
  Hom X Y := C[X, M.T.mapObj Y]
  id X := M.η.component X
  comp g f := C.comp (M.μ.component _) (C.comp (M.T.mapHom g) f)
  comp_id f := by
    have h := M.rightUnit _
    simp [h]
  id_comp f := by
    have h := M.leftUnit _
    simp [h]
  assoc f g h := by
    have h_assoc := M.associativity _
    simp [h_assoc, C.assoc]

/-! ## CoKleisli Category (for comonads) -/

def CoKleisliCat {C : Category} (W : Comonad C) : Category where
  Obj := C.Obj
  Hom X Y := C[W.L.mapObj X, Y]
  id X := W.ε.component X
  comp {X Y Z} g f := C.comp g (C.comp (W.L.mapHom g) (W.δ.component X))
  comp_id f := by
    have h := W.rightCounit _
    simp [h]
  id_comp f := by
    have h := W.leftCounit _
    simp [h]
  assoc f g h := by
    have h_coassoc := W.coassociativity _
    simp [h_coassoc, C.assoc]

/-! ## Kleisli Adjunction Free Functor -/

def kleisliFree {C : Category} (M : Monad C) : Functor C (KleisliCat M) where
  mapObj X := X
  mapHom {X Y} f := C.comp (M.η.component Y) f
  preservesId X := by
    simp [KleisliCat, C.comp_id]
  preservesComp {X Y Z} g f := by
    simp [KleisliCat, C.assoc, M.leftUnit, C.comp_id, C.id_comp]

/-! ## Kleisli Adjunction Forgetful Functor -/

def kleisliForgetful {C : Category} (M : Monad C) : Functor (KleisliCat M) C where
  mapObj X := M.T.mapObj X
  mapHom {X Y} f := C.comp (M.μ.component Y) (M.T.mapHom f)
  preservesId X := by
    simp [KleisliCat, M.rightUnit, M.T.preservesId]
  preservesComp {X Y Z} g f := by
    simp [KleisliCat, C.assoc, M.T.preservesComp, M.associativity]

/-! ## Kleisli Embedding -/

def kleisliEmbedding {C : Category} (M : Monad C) : Functor C (KleisliCat M) :=
  kleisliFree M

theorem kleisliAdjunctionProof {C : Category} (M : Monad C) : kleisliFree M ⊣ kleisliForgetful M := by
  refine {
    unit := {
      component X := M.η.component X
      naturality f := by
        simp [kleisliFree, kleisliForgetful, KleisliCat, C.assoc, M.leftUnit, M.rightUnit, C.comp_id, C.id_comp]
    }
    counit := {
      component X := C.id (M.T.mapObj X)
      naturality f := by
        simp [kleisliFree, kleisliForgetful, KleisliCat, C.assoc, M.leftUnit, M.rightUnit, C.comp_id, C.id_comp]
    }
    leftTriangle X := by
      simp [kleisliFree, kleisliForgetful, M.leftUnit, C.comp_id]
    rightTriangle X := by
      simp [kleisliFree, kleisliForgetful, M.rightUnit, M.T.preservesId, C.id_comp]
  }

/-! ## Monad Object in a 2-category (conceptual) -/

structure TwoCellProperty {C : Category} where
  source : C.Obj
  target : C.Obj

structure MonadObject {C : Category} where
  zeroCell : C.Obj
  oneCell : C[C.Obj, C.Obj]
  unitTwoCell : TwoCellProperty C
  multTwoCell : TwoCellProperty C
  leftUnitality : Prop
  rightUnitality : Prop
  associator : Prop

/-! ## Morphism of Monad Objects -/

structure MonadObjectMorphism {C : Category} (M N : MonadObject C) where
  cellComponent : Prop
  unitCompat : Prop
  multCompat : Prop

#eval "Core.Objects: KleisliCat, CoKleisliCat, kleisliFree/Forgetful"
#eval "Core.Objects: kleisliAdjunctionProof, MonadObject in 2-category"
