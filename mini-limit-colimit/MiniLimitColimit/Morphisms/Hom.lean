/-
# MiniLimitColimit.Morphisms.Hom

Morphisms of cones and cocones -- natural transformations between limiting cones.
Comparison morphisms between limits, cone category morphisms.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniNaturalTransformation.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Morphism of cones -/

structure ConeMorphism {J C : Category} {D : Diagram J C} (c₁ c₂ : Cone D) where
  apexMap : C[c₁.apex, c₂.apex]
  commutes : ∀ (j : J.Obj), C.comp (c₂.proj j) apexMap = c₁.proj j

/-! ## Morphism of cocones -/

structure CoconeMorphism {J C : Category} {D : Diagram J C} (c₁ c₂ : Cocone D) where
  nadirMap : C[c₂.nadir, c₁.nadir]
  commutes : ∀ (j : J.Obj), C.comp nadirMap (c₂.inj j) = c₁.inj j

/-! ## Identity ConeMorphism -/

def idConeMorphism {J C : Category} {D : Diagram J C} (c : Cone D) : ConeMorphism c c where
  apexMap := C.id c.apex
  commutes j := by
    simp [C.id_comp]

def idCoconeMorphism {J C : Category} {D : Diagram J C} (c : Cocone D) : CoconeMorphism c c where
  nadirMap := C.id c.nadir
  commutes j := by
    simp [C.comp_id]

/-! ## Composition of ConeMorphisms -/

def compConeMorphism {J C : Category} {D : Diagram J C} {c₁ c₂ c₃ : Cone D}
    (f : ConeMorphism c₂ c₃) (g : ConeMorphism c₁ c₂) : ConeMorphism c₁ c₃ where
  apexMap := C.comp f.apexMap g.apexMap
  commutes j := by
    rw [C.assoc, f.commutes j, g.commutes j]

def compCoconeMorphism {J C : Category} {D : Diagram J C} {c₁ c₂ c₃ : Cocone D}
    (f : CoconeMorphism c₁ c₂) (g : CoconeMorphism c₂ c₃) : CoconeMorphism c₁ c₃ where
  nadirMap := C.comp g.nadirMap f.nadirMap
  commutes j := by
    rw [← C.assoc, g.commutes j, f.commutes j]

/-! ## Comparison morphism between limits -/

/-- The canonical isomorphism from the first limit to the second, given as a cone morphism. -/
def limitComparison {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    ConeMorphism L₁.limitCone L₂.limitCone where
  apexMap := limitUniqueInv L₁ L₂
  commutes j :=
    L₂.factor L₁.limitCone j

/-- The canonical isomorphism from the first colimit to the second, given as a cocone morphism. -/
def colimitComparison {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    CoconeMorphism C₁.colimitCocone C₂.colimitCocone where
  nadirMap := colimitUniqueInv C₁ C₂
  commutes j :=
    C₁.factor C₂.colimitCocone j

/-! ## Natural transformation between diagrams induces cone morphism -/

/--
Given a natural transformation α : F ⇒ G and a cone over G, we obtain a cone over F
by precomposing the projections.
-/
def conePrecompose {J C : Category} {F G : Diagram J C} (α : NaturalTransformation F G)
    (c : Cone G) : Cone F where
  apex := c.apex
  proj j := C.comp (α.component j) (c.proj j)
  naturality {i j} u := by
    calc
      C.comp (F.mapHom u) (C.comp (α.component i) (c.proj i)) = _ := rfl
      _ = C.comp (C.comp (F.mapHom u) (α.component i)) (c.proj i) := by
        rw [C.assoc]
      _ = C.comp (C.comp (α.component j) (G.mapHom u)) (c.proj i) := by
        rw [α.naturality u]
      _ = C.comp (α.component j) (C.comp (G.mapHom u) (c.proj i)) := by
        rw [← C.assoc]
      _ = C.comp (α.component j) (c.proj j) := by
        rw [c.naturality u]

def coneMorphismFromNat {J C : Category} {F G : Diagram J C} (α : NaturalTransformation F G)
    (cG : Cone G) (cF : Cone F) (h : cF = conePrecompose α cG) : ConeMorphism cF cG where
  apexMap := C.id cG.apex
  commutes j := by
    subst h
    simp [conePrecompose, C.id_comp]

/-! ## #eval examples -/

def disc2 : Category := DiscCat (Fin 2)

def discDiagram : Diagram disc2 SetCat := Functor.const disc2 SetCat Unit

def discCone1 : Cone discDiagram where
  apex := Unit
  proj _ := fun _ => ()
  naturality _ := by
    simp [disc2, discDiagram, Functor.const, SetCat]

def discCone2 : Cone discDiagram where
  apex := Bool
  proj _ := fun _ => true
  naturality _ := by
    simp [disc2, discDiagram, Functor.const, SetCat]

def exampleConeMorphism : ConeMorphism discCone1 discCone2 where
  apexMap := fun _ => true
  commutes j := by
    simp [discCone1, discCone2, SetCat]

def exampleCoconeMorphism : CoconeMorphism
    { nadir := Unit
      inj _ := fun _ => ()
      naturality _ := by simp [SetCat]
    : Cocone discDiagram }
    { nadir := Bool
      inj _ := fun _ => true
      naturality _ := by simp [SetCat]
    : Cocone discDiagram } where
  nadirMap := fun _ => ()
  commutes j := by simp [SetCat]

#eval "Morphisms.Hom: ConeMorphism, CoconeMorphism, limitComparison"
#eval exampleConeMorphism.apexMap ()
#eval compConeMorphism (idConeMorphism discCone1) exampleConeMorphism |>.apexMap ()
#eval exampleCoconeMorphism.nadirMap true

end MiniLimitColimit
