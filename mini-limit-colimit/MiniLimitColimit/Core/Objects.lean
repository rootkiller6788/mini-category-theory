/-
# MiniLimitColimit.Core.Objects

Limit and Colimit structures — terminal/initial objects in cone categories.
-/

import MiniCategoryCore.Core.Basic
import MiniLimitColimit.Core.Basic

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Limit -/

structure Limit {J C : Category} (D : Diagram J C) where
  limitCone : Cone D
  mediate : ∀ (c : Cone D), C[c.apex, limitCone.apex]
  factor : ∀ (c : Cone D) (j : J.Obj),
    C.comp (limitCone.proj j) (mediate c) = c.proj j
  unique : ∀ (c : Cone D) (f : C[c.apex, limitCone.apex]),
    (∀ (j : J.Obj), C.comp (limitCone.proj j) f = c.proj j) → f = mediate c

/-! ## Colimit -/

structure Colimit {J C : Category} (D : Diagram J C) where
  colimitCocone : Cocone D
  mediate : ∀ (c : Cocone D), C[colimitCocone.nadir, c.nadir]
  factor : ∀ (c : Cocone D) (j : J.Obj),
    C.comp (mediate c) (colimitCocone.inj j) = c.inj j
  unique : ∀ (c : Cocone D) (f : C[colimitCocone.nadir, c.nadir]),
    (∀ (j : J.Obj), C.comp f (colimitCocone.inj j) = c.inj j) → f = mediate c

def exDiagram : Diagram (DiscCat Unit) SetCat := Functor.const (DiscCat Unit) SetCat Unit

def exLimit : Limit exDiagram where
  limitCone := {
    apex := Unit
    proj _ := fun _ => ()
    naturality _ := by simp
  }
  mediate _ := fun _ => ()
  factor _ _ := rfl
  unique _ _ _ := by funext x; simp

def exColimit : Colimit exDiagram where
  colimitCocone := {
    nadir := Unit
    inj _ := fun _ => ()
    naturality _ := by simp
  }
  mediate _ := fun _ => ()
  factor _ _ := rfl
  unique _ _ _ := by funext x; simp

#eval "Core.Objects: Limit, Colimit"
#eval exLimit.limitCone.apex
#eval exColimit.colimitCocone.nadir
#eval exLimit.mediate exLimit.limitCone ()
