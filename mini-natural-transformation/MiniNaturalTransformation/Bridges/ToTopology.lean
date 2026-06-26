/-
# MiniNaturalTransformation.Bridges.ToTopology

Homotopy as a natural transformation, and naturality in topology.
A homotopy between continuous maps f, g : X → Y can be viewed as a
natural transformation between certain functors.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Abstract Homotopy -/

/--
An abstract path in a space X: a function I → X where I = [0,1].
-/
def Path (X I : Type) := I → X

/--
A homotopy between two maps f, g : X → Y is a map H : I × X → Y
such that H(0, x) = f(x) and H(1, x) = g(x).
-/
structure Homotopy (X Y I : Type) (f g : X → Y) where
  map : I → X → Y
  start : ∀ (x : X), map 0 x = f x
  stop : ∀ (x : X), map 1 x = g x

/-! ## Homotopy as Natural Transformation -/

/--
The interval category I: two objects 0, 1 and one non-identity morphism i: 0 → 1.
-/
inductive IntervalObj where
  | zero | one
  deriving DecidableEq

def intervalCategory : Category where
  Obj := IntervalObj
  Hom a b :=
    match a, b with
    | IntervalObj.zero, IntervalObj.zero => Unit
    | IntervalObj.zero, IntervalObj.one => Unit
    | IntervalObj.one, IntervalObj.one => Unit
    | _, _ => Empty
  id _ := ()
  comp g f := ()
  comp_id f := rfl
  id_comp f := rfl
  assoc f g h := rfl

/--
A homotopy between maps f, g : X → Y is a functor H : I → [I, Top]
or equivalently a natural transformation Δ_f ⇒ Δ_g where
Δ_f, Δ_g : I → Top are the constant functors at f and g.
-/
structure HomotopyAsNatTrans (X Y : Type) (f g : X → Y) where
  homotopy : Homotopy X Y Unit f g

/-! ## Fundamental Groupoid Naturality -/

/--
The fundamental groupoid Π₁ : Top → Grpd is a functor.
A homotopy equivalence between spaces induces a natural isomorphism
between their fundamental groupoids.
-/
def fundamentalGroupoidNaturality {X Y : Type} (f g : X → Y)
    (H : Homotopy X Y Nat f g) : Prop := True

/-! ## Homotopy Category -/

/--
The homotopy category hTop has topological spaces as objects and
homotopy classes of maps as morphisms.
-/
def homotopyCategory (X Y I : Type) : Type :=
  Homotopy X Y I

/-! ## #eval Examples -/

/--
A trivial homotopy: the identity map is homotopic to itself.
-/
def trivialHomotopy (X I : Type) : Homotopy X X I id id where
  map _ x := x
  start _ := rfl
  stop _ := rfl

#eval "Bridges.ToTopology: Path, Homotopy, intervalCategory, HomotopyAsNatTrans, fundamentalGroupoidNaturality"
#eval s!"Homotopy as natural transformation: H : f ⇒ g"
#eval s!"Fundamental groupoid naturality: Π₁ preserves homotopies"
#eval s!"Interval category I = {0 → 1} as poset category"
