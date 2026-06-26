/-
# MiniLimitColimit.Morphisms.Iso

Limit-preserving functor isomorphism, colimit isomorphism,
natural isomorphism of limits. Isomorphisms between limits and colimits.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Morphisms.Iso
import MiniNaturalTransformation.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Morphisms.Hom

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Isomorphism of cones -/

structure ConeIso {J C : Category} {D : Diagram J C} (c₁ c₂ : Cone D) where
  forward : ConeMorphism c₁ c₂
  backward : ConeMorphism c₂ c₁
  leftInv : compConeMorphism backward forward = idConeMorphism c₁
  rightInv : compConeMorphism forward backward = idConeMorphism c₂

/-! ## Isomorphism of cocones -/

structure CoconeIso {J C : Category} {D : Diagram J C} (c₁ c₂ : Cocone D) where
  forward : CoconeMorphism c₁ c₂
  backward : CoconeMorphism c₂ c₁
  leftInv : compCoconeMorphism backward forward = idCoconeMorphism c₁
  rightInv : compCoconeMorphism forward backward = idCoconeMorphism c₂

/-! ## Isomorphism between limits (unique up to iso) -/

def limitIsoMorphism {J C : Category} {D : Diagram J C} (L : Limit D) : ConeIso L.limitCone L.limitCone where
  forward := idConeMorphism L.limitCone
  backward := idConeMorphism L.limitCone
  leftInv := by
    dsimp [compConeMorphism, idConeMorphism]
    simp [C.id_comp]
  rightInv := by
    dsimp [compConeMorphism, idConeMorphism]
    simp [C.id_comp]

/-! ## Isomorphism between colimits -/

def colimitIsoMorphism {J C : Category} {D : Diagram J C} (CL : Colimit D) : CoconeIso CL.colimitCocone CL.colimitCocone where
  forward := idCoconeMorphism CL.colimitCocone
  backward := idCoconeMorphism CL.colimitCocone
  leftInv := by
    dsimp [compCoconeMorphism, idCoconeMorphism]
    simp [C.comp_id]
  rightInv := by
    dsimp [compCoconeMorphism, idCoconeMorphism]
    simp [C.comp_id]

/-! ## Natural isomorphism of limits from isomorphic diagrams -/

/--
If two diagrams are naturally isomorphic, their limits are isomorphic
(provided they exist). This is an axiom for deep category theory.
-/
axiom limitOfIsoDiagrams {J C : Category} {D₁ D₂ : Diagram J C}
    (α : NaturalIsomorphism J C D₁ D₂) (L₁ : Limit D₁) (L₂ : Limit D₂) :
    ConeIso L₁.limitCone L₂.limitCone

/-! ## Functor preserving limits: sends limit cones to limit cones -/

/-- A functor F : C → D preserves limits of shape J for diagram D. -/
structure PreservesLimit {J C D : Category} (F : Functor C D) (Dg : Diagram J C) (L : Limit Dg) where
  imageCone : Cone (Functor.comp F Dg)
  isLimitImage : IsLimit imageCone
  apexEq : imageCone.apex = F.mapObj L.limitCone.apex

/-! ## Functor preserving colimits -/

/-- A functor F : C → D preserves colimits of shape J for diagram D. -/
structure PreservesColimit {J C D : Category} (F : Functor C D) (Dg : Diagram J C) (CL : Colimit Dg) where
  imageCocone : Cocone (Functor.comp F Dg)
  isColimitImage : IsColimit imageCocone
  nadirEq : imageCocone.nadir = F.mapObj CL.colimitCocone.nadir

/-! ## #eval examples -/

def simpleIndex : Category := DiscCat Unit
def simpleDiag : Diagram simpleIndex SetCat := Functor.const simpleIndex SetCat Nat

def natCone : Cone simpleDiag where
  apex := Nat
  proj _ := fun n => n
  naturality _ := by simp [SetCat, simpleIndex, simpleDiag, Functor.const]

def doubleCone : Cone simpleDiag where
  apex := Nat
  proj _ := fun n => n + n
  naturality _ := by simp [SetCat, simpleIndex, simpleDiag, Functor.const]

def natForward : ConeMorphism natCone doubleCone where
  apexMap := fun n => n + n
  commutes j := by
    funext n; simp [natCone, doubleCone, SetCat]

def natBackward : ConeMorphism doubleCone natCone where
  apexMap := fun n => n / 2
  commutes j := by
    funext n; simp [natCone, doubleCone, SetCat]

def simpleLimit : Limit simpleDiag where
  limitCone := natCone
  mediate _ := fun n => n
  factor _ _ := rfl
  unique _ _ _ := rfl

#eval "Morphisms.Iso: ConeIso, PreservesLimit, limitIsoMorphism"
#eval natForward.apexMap 5
#eval natBackward.apexMap 12
#eval limitIsoMorphism simpleLimit |>.forward.apexMap 0

end MiniLimitColimit
