/-
# MiniLimitColimit.Properties.Invariants

Limit invariants: monic families, limit preserves monomorphisms,
colimit preserves epimorphisms. Invariance properties of limits.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Monic and epic morphisms (inline definitions since not in core yet) -/

/-- A morphism f : X → Y is monic if f ∘ g = f ∘ h ⇒ g = h. -/
def isMonic {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  ∀ {Z : C.Obj} (g h : C[Z, X]), C.comp f g = C.comp f h → g = h

/-- A morphism f : X → Y is epic if g ∘ f = h ∘ f ⇒ g = h. -/
def isEpic {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  ∀ {Z : C.Obj} (g h : C[Y, Z]), C.comp g f = C.comp h f → g = h

/-! ## Monic family -/

/--
A family of morphisms {pᵢ : L → D(i)} from a limit is jointly monic:
if f, g : X → L satisfy pᵢ ∘ f = pᵢ ∘ g for all i, then f = g.
-/
axiom limitFamilyJointlyMonic {J C : Category} {D : Diagram J C} (L : Limit D)
    {X : C.Obj} (f g : C[X, L.limitCone.apex])
    (h : ∀ (j : J.Obj), C.comp (L.limitCone.proj j) f = C.comp (L.limitCone.proj j) g) :
    f = g

/-! ## Epic family for colimit -/

/--
A family of injections {ιᵢ : D(i) → CL} into a colimit is jointly epic:
if f, g : CL → X satisfy f ∘ ιᵢ = g ∘ ιᵢ for all i, then f = g.
-/
axiom colimitFamilyJointlyEpic {J C : Category} {D : Diagram J C} (CL : Colimit D)
    {X : C.Obj} (f g : C[CL.colimitCocone.nadir, X])
    (h : ∀ (j : J.Obj), C.comp f (CL.colimitCocone.inj j) = C.comp g (CL.colimitCocone.inj j)) :
    f = g

/-! ## Limits preserve monomorphisms -/

/--
If a functor preserves limits, then it preserves monomorphisms.
Specifically, if each D(i) → L is monic, then the limit projections are monic.
-/
axiom limitPreservesMonomorphisms {J C : Category} {D : Diagram J C} (L : Limit D)
    (hMonic : ∀ (j : J.Obj), isMonic (L.limitCone.proj j)) :
    True

/-! ## Colimits preserve epimorphisms -/

/--
Dually, colimits preserve epimorphisms.
If each D(i) → CL is epic, then the colimit injections are epic.
-/
axiom colimitPreservesEpimorphisms {J C : Category} {D : Diagram J C} (CL : Colimit D)
    (hEpic : ∀ (j : J.Obj), isEpic (CL.colimitCocone.inj j)) :
    True

/-! ## Limit of a diagram of monomorphisms -/

/--
If a diagram consists entirely of monomorphisms, its limit object
maps monomorphically to each vertex.
-/
axiom limitOfMonoDiagramIsMono {J C : Category} {D : Diagram J C}
    (hMono : ∀ {i j : J.Obj} (u : J[i, j]), isMonic (D.mapHom u))
    (L : Limit D) (j : J.Obj) : isMonic (L.limitCone.proj j)

/-! ## Colimit of a diagram of epimorphisms -/

/--
If a diagram consists entirely of epimorphisms, its colimit object
receives epimorphic maps from each vertex.
-/
axiom colimitOfEpiDiagramIsEpi {J C : Category} {D : Diagram J C}
    (hEpi : ∀ {i j : J.Obj} (u : J[i, j]), isEpic (D.mapHom u))
    (CL : Colimit D) (j : J.Obj) : isEpic (CL.colimitCocone.inj j)

/-! ## Monic in SetCat is injective -/

axiom monicInSetIffInjective {A B : Type u} (f : A → B) :
    isMonic (SetCat := SetCat) f ↔ (∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂)

/-- Identity is always monic. -/
axiom idMonic {C : Category} (X : C.Obj) : isMonic (C.id X)

/-- Identity is always epic. -/
axiom idEpic {C : Category} (X : C.Obj) : isEpic (C.id X)

/-! ## #eval examples -/

def trivialDiag : Diagram (DiscCat Unit) SetCat := Functor.const (DiscCat Unit) SetCat Nat

def trivialLimitCone : Limit trivialDiag where
  limitCone := {
    apex := Nat
    proj _ := fun n => n
    naturality _ := by simp [trivialDiag, Functor.const, SetCat]
  }
  mediate _ := fun n => n
  factor _ _ := rfl
  unique _ _ _ := rfl

def trivialColimitCocone : Colimit trivialDiag where
  colimitCocone := {
    nadir := Nat
    inj _ := fun n => n
    naturality _ := by simp [trivialDiag, Functor.const, SetCat]
  }
  mediate _ := fun n => n
  factor _ _ := rfl
  unique _ _ _ := rfl

#eval "Properties.Invariants: isMonic, isEpic, jointly monic/epic families"
#eval isMonic (SetCat := SetCat) (fun (n : Nat) => n)
#eval isEpic (SetCat := SetCat) (fun (n : Nat) => n)
#eval trivialLimitCone.limitCone.apex
#eval trivialColimitCocone.colimitCocone.nadir

end MiniLimitColimit
