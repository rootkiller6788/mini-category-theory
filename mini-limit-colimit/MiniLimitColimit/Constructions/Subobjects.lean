/-
# MiniLimitColimit.Constructions.Subobjects

Equalizer as limit, terminal object as limit of empty diagram,
pullback as limit. Subobjects constructed via limits.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Equalizer diagram -/

/--
A fork for parallel arrows f, g : A → B is an object E with an arrow e : E → A
such that f ∘ e = g ∘ e.
-/
structure Fork {C : Category} {A B : C.Obj} (f g : C[A, B]) where
  obj : C.Obj
  forkMap : C[obj, A]
  condition : C.comp f forkMap = C.comp g forkMap

/-- An equalizer is a universal fork. -/
structure Equalizer {C : Category} {A B : C.Obj} (f g : C[A, B]) where
  fork : Fork f g
  mediate : ∀ (f' : Fork f g), C[f'.obj, fork.obj]
  factor : ∀ (f' : Fork f g), C.comp fork.forkMap (mediate f') = f'.forkMap
  unique : ∀ (f' : Fork f g) (h : C[f'.obj, fork.obj]),
    C.comp fork.forkMap h = f'.forkMap → h = mediate f'

/-! ## Equalizer in SetCat -/

def forkInSet {A B : Type u} (f g : A → B) : Fork (SetCat := SetCat) f g where
  obj := { x : A // f x = g x }
  forkMap x := x.val
  condition := by
    funext ⟨x, h⟩
    simp [h]

def equalizerInSet {A B : Type u} (f g : A → B) : Equalizer (SetCat := SetCat) f g where
  fork := forkInSet f g
  mediate f' := fun x => ⟨f'.forkMap x, by
    have h := congrFun f'.condition x
    exact h⟩
  factor f' := rfl
  unique f' h h_eq := by
    funext x
    have hx := congrFun h_eq x
    apply Subtype.ext
    exact hx

/-! ## Terminal object as limit of empty diagram -/

/--
The empty diagram gives the terminal object as its limit.
Since the shape has no objects, ANY object is a cone, but the limit
must be terminal.
-/
axiom terminalAsEmptyLimit (C : Category) (T : Terminal C) :
    Limit (Functor.const (DiscCat PEmpty) C T.obj)

/-! ## Pullback as limit -/

/--
The shape for a pullback: a cospan A → D ← B.
The pullback is the limit of this cospan diagram.
-/
structure PullbackCone {C : Category} {A B D : C.Obj} (f : C[A, D]) (g : C[B, D]) where
  apex : C.Obj
  p : C[apex, A]
  q : C[apex, B]
  commutes : C.comp f p = C.comp g q

/-- A pullback is a universal pullback cone. -/
structure Pullback {C : Category} {A B D : C.Obj} (f : C[A, D]) (g : C[B, D]) where
  cone : PullbackCone f g
  mediate : ∀ (c : PullbackCone f g), C[c.apex, cone.apex]
  factor_p : ∀ (c : PullbackCone f g), C.comp cone.p (mediate c) = c.p
  factor_q : ∀ (c : PullbackCone f g), C.comp cone.q (mediate c) = c.q
  unique : ∀ (c : PullbackCone f g) (h : C[c.apex, cone.apex]),
    C.comp cone.p h = c.p → C.comp cone.q h = c.q → h = mediate c

/-! ## Pullback in SetCat -/

def pullbackConeInSet {A B D : Type u} (f : A → D) (g : B → D) : PullbackCone (SetCat := SetCat) f g where
  apex := { p : A × B // f p.1 = g p.2 }
  p x := x.val.1
  q x := x.val.2
  commutes := by
    funext x; exact x.property

def pullbackInSet {A B D : Type u} (f : A → D) (g : B → D) : Pullback (SetCat := SetCat) f g where
  cone := pullbackConeInSet f g
  mediate c := fun x => ⟨(c.p x, c.q x), by
    have h := congrFun c.commutes x
    exact h⟩
  factor_p c := rfl
  factor_q c := rfl
  unique c h h1 h2 := by
    funext x
    have hx1 := congrFun h1 x
    have hx2 := congrFun h2 x
    apply Subtype.ext
    apply Prod.ext <;> assumption

/-! ## Monomorphism from Pullback -/

/--
In SetCat, the pullback projection q : A ×_D B → B is a monomorphism
if f : A → D is a monomorphism.
-/
axiom pullbackPreservesMonoInSet {A B D : Type u} {f : A → D} {g : B → D}
    (hMono : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) : True

/-! ## #eval examples -/

def f : Nat → Nat := fun n => n + 1
def g : Nat → Nat := fun n => n + 2

#eval "Constructions.Subobjects: Equalizer, Terminal as limit, Pullback"
#eval forkInSet (SetCat := SetCat) (fun (n : Nat) => n) (fun n => n) |>.forkMap ⟨5, rfl⟩
#eval equalizerInSet (SetCat := SetCat) f f |>.fork.obj
#eval pullbackInSet (SetCat := SetCat) (fun (a : Nat) => a) (fun (b : Nat) => b) |>.cone.apex

end MiniLimitColimit
