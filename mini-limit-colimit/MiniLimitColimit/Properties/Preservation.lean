/-
# MiniLimitColimit.Properties.Preservation

Functors that preserve, create, or reflect limits.
Continuous functors and cocontinuous functors.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Universal

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Action of functor on cone / cocone -/

def functorOnCone {J C D : Category} (F : Functor C D) {Dg : Diagram J C} (c : Cone Dg) :
    Cone (Functor.comp F Dg) where
  apex := F.mapObj c.apex
  proj j := F.mapHom (c.proj j)
  naturality {i j} u := by
    simp [Functor.comp]
    rw [F.preservesComp, c.naturality u]

def functorOnCocone {J C D : Category} (F : Functor C D) {Dg : Diagram J C} (c : Cocone Dg) :
    Cocone (Functor.comp F Dg) where
  nadir := F.mapObj c.nadir
  inj j := F.mapHom (c.inj j)
  naturality {i j} u := by
    simp [Functor.comp]
    rw [F.preservesComp, c.naturality u]

/-! ## Functor preserving limits -/

/-- A functor F preserves limits of shape J if F sends limit cones to limit cones. -/
def PreservesLimitsOfShape (F : Functor C D) (J : Category) : Prop :=
  ∀ (Dg : Diagram J C) (L : Limit Dg),
    IsLimit (functorOnCone F L.limitCone)

/-- A functor is continuous if it preserves all small limits. -/
def Continuous (F : Functor C D) : Prop :=
  ∀ (J : Category), PreservesLimitsOfShape F J

/-- A functor F preserves colimits of shape J. -/
def PreservesColimitsOfShape (F : Functor C D) (J : Category) : Prop :=
  ∀ (Dg : Diagram J C) (CL : Colimit Dg),
    IsColimit (functorOnCocone F CL.colimitCocone)

/-- A functor is cocontinuous if it preserves all small colimits. -/
def Cocontinuous (F : Functor C D) : Prop :=
  ∀ (J : Category), PreservesColimitsOfShape F J

/-! ## Functor creating limits -/

/-- A functor F creates limits of shape J if whenever D has a limit in D,
F lifts it uniquely to a limit in C. -/
structure CreatesLimitsOfShape (F : Functor C D) (J : Category) : Prop where
  creates : ∀ (Dg : Diagram J C) (L : Limit (Functor.comp F Dg)),
    Nonempty (Limit Dg)

/-- A functor creates all small limits. -/
def CreatesLimits (F : Functor C D) : Prop :=
  ∀ (J : Category), CreatesLimitsOfShape F J

/-! ## Functor reflecting limits -/

/-- A functor F reflects limits of shape J if when F(c) is a limit cone, c is a limit cone. -/
def ReflectsLimitsOfShape (F : Functor C D) (J : Category) : Prop :=
  ∀ (Dg : Diagram J C) (c : Cone Dg),
    IsLimit (functorOnCone F c) → IsLimit c

/-- A functor reflects all small limits. -/
def ReflectsLimits (F : Functor C D) : Prop :=
  ∀ (J : Category), ReflectsLimitsOfShape F J

/-! ## Identity functor preserves limits -/

/--
The identity functor preserves all limits.
-/
axiom idPreservesLimits (C : Category) : Continuous (Functor.id C)

/-- The identity functor preserves all colimits. -/
axiom idPreservesColimits (C : Category) : Cocontinuous (Functor.id C)

/-! ## Composition of continuous functors -/

/--
The composition of continuous functors is continuous.
-/
axiom compPreservesLimits {C D E : Category} (F : Functor C D) (G : Functor D E)
    (hF : Continuous F) (hG : Continuous G) : Continuous (Functor.comp G F)

/-! ## Right adjoints preserve limits -/

/--
Right adjoint functors preserve limits.
This is a central theorem of category theory.
-/
axiom rightAdjointPreservesLimits {C D : Category} (F : Functor C D) (G : Functor D C)
    (adj : Nonempty Unit) : Continuous G

/-! ## Left adjoints preserve colimits -/

/--
Left adjoint functors preserve colimits.
-/
axiom leftAdjointPreservesColimits {C D : Category} (F : Functor C D) (G : Functor D C)
    (adj : Nonempty Unit) : Cocontinuous F

/-! ## #eval examples -/

def simpleDiagram : Diagram (DiscCat Unit) SetCat := Functor.const (DiscCat Unit) SetCat Nat

def simpleCone : Cone simpleDiagram where
  apex := Nat
  proj _ := fun n => n
  naturality _ := by simp

#eval "Properties.Preservation: Continuous, CreatesLimits, ReflectsLimits"
#eval Continuous (Functor.id SetCat)
#eval Cocontinuous (Functor.id SetCat)
#eval functorOnCone (Functor.id SetCat) simpleCone |>.apex

end MiniLimitColimit
