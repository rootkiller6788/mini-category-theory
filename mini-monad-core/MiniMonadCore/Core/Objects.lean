/-
# MiniMonadCore.Core.Objects

Kleisli category: given a monad M on C, the Kleisli category Kl(M)
has objects of C and morphisms Kl_M(X, Y) = C[X, M.T(Y)].
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem

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

#eval "Core.Objects: KleisliCat construction"
