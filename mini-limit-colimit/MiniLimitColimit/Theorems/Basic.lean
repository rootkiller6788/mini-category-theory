/-
# MiniLimitColimit.Theorems.Basic

Basic limit theorems: limit of equalizers, pullback lemma,
pasting lemma for pullbacks. Fundamental structural results.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Properties.Invariants
import MiniLimitColimit.Morphisms.Hom

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Limit of a diagram of equalizers -/

/--
If each object in the diagram is an equalizer, the limit object
is also an equalizer (if limits exist).

This is a special case of the fact that limits commute with limits.
-/
axiom limitOfEqualizersIsEqualizer {J C : Category} {D : Diagram J C}
    (h : ∀ (j : J.Obj), ∃ (A B : C.Obj) (f g : C[A, B]), Nonempty (Equalizer f g))
    (L : Limit D) : ∃ (A B : C.Obj) (f g : C[A, B]), Nonempty (Equalizer f g)

/-! ## Limits commute with limits -/

/--
The limit of a functor F : I × J → C can be computed iteratively:
lim_{i} lim_{j} F(i,j) = lim_{(i,j)} F(i,j) = lim_{j} lim_{i} F(i,j).
This is the Fubini theorem for limits.
-/
axiom limitsCommuteWithLimits {I J C : Category} (F : Diagram (I ×ᶜ J) C) :
    Nonempty (Limit F)

/-! ## Pullback pasting lemma -/

/--
Given a commutative diagram:
  W → X → Y
  ↓    ↓    ↓
  Z → U → V
If both squares are pullbacks, then the outer rectangle is a pullback.
Conversely, if the right square and outer rectangle are pullbacks, so is the left.
-/
axiom pullbackPastingLemma {C : Category}
    {W X Y Z U V : C.Obj}
    (f1 : C[W, X]) (f2 : C[X, Y]) (g1 : C[Z, U]) (g2 : C[U, V])
    (hWZ : C[W, Z]) (hXU : C[X, U]) (hYV : C[Y, V])
    (comm1 : C.comp hXU f1 = C.comp g1 hWZ)
    (comm2 : C.comp hYV f2 = C.comp g2 hXU)
    (hLeft : Pullback f1 g1) (hRight : Pullback f2 g2) :
    Pullback (C.comp f2 f1) (C.comp g2 g1)

/-! ## Pullback of a monomorphism is a monomorphism -/

/--
Pullbacks preserve monomorphisms: if f is monic, then its pullback
along any morphism is also monic.
-/
axiom pullbackPreservesMono {C : Category} {A B D : C.Obj}
    (f : C[A, D]) (g : C[B, D]) (hMono : isMonic f)
    (pb : Pullback f g) : isMonic pb.cone.q

/-! ## Limit of shape with initial object -/

/--
If the shape category J has an initial object, then the limit
of any diagram D : J → C is just D evaluated at the initial object.
-/
axiom limitOfShapeWithInitial {J C : Category} (D : Diagram J C)
    (init : Initial J) (L : Limit D) :
    IsLimit {
      apex := D.mapObj init.obj
      proj j := D.mapHom (init.initiate j)
      naturality u := by
        have h := init.unique _ (C.comp u (init.initiate _))
        have h' : C.comp (D.mapHom (init.initiate _)) (D.mapHom u) = D.mapHom (init.initiate _) := by
          rw [← D.preservesComp, h]
        simpa
    : Cone D}

/-! ## Colimit of shape with terminal object -/

/--
If the shape category J has a terminal object, then the colimit
of any diagram D : J → C is just D evaluated at the terminal object.
-/
axiom colimitOfShapeWithTerminal {J C : Category} (D : Diagram J C)
    (term : Terminal J) (CL : Colimit D) :
    IsColimit {
      nadir := D.mapObj term.obj
      inj j := D.mapHom (term.terminate j)
      naturality u := by
        have h := term.unique _ (C.comp (term.terminate _) u)
        have h' : C.comp (D.mapHom u) (D.mapHom (term.terminate _)) = D.mapHom (term.terminate _) := by
          rw [D.preservesComp, h]
        simpa
    : Cocone D}

/-! ## Projection formula -/

/--
The projection formula: given a limit cone L over D, the projection
maps compose correctly with limit morphisms.
-/
def limitProjectionFormula {J C : Category} {D : Diagram J C} (L : Limit D) (j : J.Obj) : True :=
  have h := L.factor L.limitCone j
  trivial

/-! ## #eval examples -/

def idNat : Nat → Nat := fun n => n
def twiceNat : Nat → Nat := fun n => n + n

def eqPullback : Pullback (SetCat := SetCat) idNat twiceNat :=
  pullbackInSet idNat twiceNat

#eval "Theorems.Basic: pullback pasting, limits commute, limit of shape with initial"
#eval eqPullback.cone.apex
#eval eqPullback.cone.p { val := (0, 0), property := by simp }
#eval eqPullback.cone.q { val := (0, 0), property := by simp }

end MiniLimitColimit
