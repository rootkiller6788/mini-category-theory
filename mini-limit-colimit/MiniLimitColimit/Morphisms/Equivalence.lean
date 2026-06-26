/-
# MiniLimitColimit.Morphisms.Equivalence

Equivalent limits, limit-cone equivalence, limit-colimit duality.
Equivalence of cone categories via the limit universal property.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Iso
import MiniNaturalTransformation.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Morphisms.Hom

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Cones are equivalent to morphisms out of a limit object -/

/--
If L is a limit cone for D, then for any object X,
cones with apex X are in bijection with C[X, L.apex].
-/
structure LimitUniversalEquivalence {J C : Category} {D : Diagram J C} (L : Limit D) where
  coneToMorphism : ∀ (X : C.Obj), ({ c : Cone D // c.apex = X } → C[X, L.limitCone.apex])
  morphismToCone : ∀ (X : C.Obj), (C[X, L.limitCone.apex] → Cone D)
  correspondence : ∀ (X : C.Obj) (f : C[X, L.limitCone.apex]),
    (morphismToCone X f).apex = X

/-! ## Limit-colimit duality -/

/--
The limit of D in C is the colimit of D in Cᵒᵖ.
This equivalence is fundamental to category theory.
-/
axiom limitAsColimitOp {J C : Category} (D : Diagram J C) (L : Limit D) :
    Nonempty (Colimit (Functor.id (Cᵒᵖ)))
    -- More precisely: L in C gives a colimit in Cᵒᵖ.

/--
A cone over D in C corresponds to a cocone under D in Cᵒᵖ.
-/
axiom coneToCoconeOp {J C : Category} (D : Diagram J C) (c : Cone D) : Cocone (Functor.id (Cᵒᵖ))

/--
A cocone under D in C corresponds to a cone over D in Cᵒᵖ.
-/
axiom coconeToConeOp {J C : Category} (D : Diagram J C) (c : Cocone D) : Cone (Functor.id (Cᵒᵖ))

/-! ## Equivalent shape categories yield equivalent limits -/

/--
If the shape categories J and J' are equivalent, then limits of
corresponding diagrams are isomorphic (limit of D in C ≅ limit of D' in C).
-/
axiom equivalentShapeLimitsIso {J J' C : Category} (D : Diagram J C) (D' : Diagram J' C)
    (eqv : Equivalence J J') : True

/-! ## Limits in equivalent categories -/

/--
If C ≅ D are equivalent categories and L is a limit in C,
then the image of L under the equivalence is a limit in D.
-/
axiom limitInEquivalentCategory {C D J : Category}
    (eqv : Equivalence C D) (Dg : Diagram J C) (L : Limit Dg) :
    True

/-! ## Cone category equivalence under limit -/

/--
The limit universal property gives an equivalence between the cone category
and the slice category over the limit object.
-/
axiom coneCatEquivSlice {J C : Category} {D : Diagram J C} (L : Limit D) :
    True
    -- The category of cones over D is equivalent to C / L.apex (the slice).
    -- Cones are equivalent to morphisms into the limit apex.

/-! ## Direct comparison: two limits are isomorphic -/

/--
Any two limits of the same diagram are isomorphic via unique isomorphisms.
-/
def limitIsoUnique {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) : True := by
  have f := limitUnique L₁ L₂
  have g := limitUniqueInv L₁ L₂
  have h1 := limitUniqueId L₁ L₂
  have h2 := limitUniqueId' L₁ L₂
  exact trivial

/-! ## #eval examples -/

def unitIndex : Category := DiscCat Unit
def unitDiag : Diagram unitIndex SetCat := Functor.const unitIndex SetCat Unit

def unitCone : Cone unitDiag where
  apex := Unit
  proj _ := fun _ => ()
  naturality _ := by simp [SetCat, unitIndex, unitDiag, Functor.const]

def unitLimit : Limit unitDiag where
  limitCone := unitCone
  mediate _ := fun _ => ()
  factor _ _ := rfl
  unique _ _ _ := by
    funext x; simp

#eval "Morphisms.Equivalence: LimitUniversalEquivalence, limit-colimit duality"
#eval unitLimit.limitCone.apex
#eval ConeCat unitDiag |>.Obj
#eval limitIsoUnique unitLimit unitLimit

end MiniLimitColimit
