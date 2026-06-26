/-
# MiniMorphismSystem.Core.Basic

Functors between categories: maps on objects and morphisms that
preserve identity and composition.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Functor -/

structure Functor (C D : Category) where
  mapObj : C.Obj → D.Obj
  mapHom : {X Y : C.Obj} → C[X, Y] → D[mapObj X, mapObj Y]
  preservesId : ∀ (X : C.Obj), mapHom (C.id X) = D.id (mapObj X)
  preservesComp : ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]),
    mapHom (C.comp f g) = D.comp (mapHom f) (mapHom g)

notation:60 F:60 "[" X:60 "]" => Functor.mapObj F X
notation:60 F:60 "⟦" f:60 "⟧" => Functor.mapHom F f

/-! ## Constant Functor -/

def Functor.const (C D : Category) (d : D.Obj) : Functor C D where
  mapObj _ := d
  mapHom _ := D.id d
  preservesId _ := rfl
  preservesComp _ _ := by
    simp [D.id_comp]

#eval "Core.Basic: Functor, Functor.const"
