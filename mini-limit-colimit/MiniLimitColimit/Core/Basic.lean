/-
# MiniLimitColimit.Core.Basic

Diagrams, cones, cocones. The fundamental definitions for limits and colimits.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Diagram -/

abbrev Diagram (J C : Category) := Functor J C

/-! ## Cone over a Diagram -/

structure Cone {J C : Category} (D : Diagram J C) where
  apex : C.Obj
  proj : ∀ (j : J.Obj), C[apex, D.mapObj j]
  naturality : ∀ {i j : J.Obj} (u : J[i, j]),
    C.comp (D.mapHom u) (proj i) = proj j

/-! ## Cocone under a Diagram -/

structure Cocone {J C : Category} (D : Diagram J C) where
  nadir : C.Obj
  inj : ∀ (j : J.Obj), C[D.mapObj j, nadir]
  naturality : ∀ {i j : J.Obj} (u : J[i, j]),
    C.comp (inj j) (D.mapHom u) = inj i

/-! ## Cones form a category -/

def ConeCat {J C : Category} (D : Diagram J C) : Category where
  Obj := Cone D
  Hom c₁ c₂ := { f : C[c₁.apex, c₂.apex] //
    ∀ (j : J.Obj), C.comp (c₂.proj j) f = c₁.proj j }
  id c := ⟨C.id c.apex, fun j => by simp [C.id_comp]⟩
  comp g f := ⟨C.comp g.1 f.1, fun j => by
    rcases g with ⟨g', hg⟩; rcases f with ⟨f', hf⟩
    simp [C.assoc, hg j, hf j]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

#eval "Core.Basic: Diagram, Cone, Cocone, ConeCat"

def exCone : Cone (Functor.const (DiscCat Unit) SetCat Unit) where
  apex := Unit
  proj _ := fun _ => ()
  naturality _ := by simp

def exCocone : Cocone (Functor.const (DiscCat Unit) SetCat Unit) where
  nadir := Unit
  inj _ := fun _ => ()
  naturality _ := by simp

#eval exCone.apex
#eval exCocone.nadir
#eval ConeCat (Functor.const (DiscCat Unit) SetCat Unit) |>.Obj
