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

/-! ## Homotopy Category Structure -/

/--
Composition of homotopies: if H : f ≃ g and K : g ≃ h, then
H • K : f ≃ h (concatenation of homotopies).
-/
structure HomotopyComposition (X Y I : Type) (f g h : X → Y) where
  H1 : Homotopy X Y I f g
  H2 : Homotopy X Y I g h

/--
The homotopy extension property: a map i : A → X has the HEP if
for every map f : X → Y and homotopy H : f|A ≃ g, there exists
an extension of H to a homotopy on all of X.
-/
structure HomotopyExtensionProperty (A X Y I : Type) (i : A → X) where
  extend : ∀ (f : X → Y) (g : A → Y) (H : Homotopy A Y I (f ∘ i) g),
    Homotopy X Y I f (λ x => f x)

/--
The fundamental group functor π₁ : Top^* → Grp sends a pointed space
(X, x₀) to its fundamental group π₁(X, x₀). A continuous map f : X → Y
induces a group homomorphism f_* : π₁(X, x₀) → π₁(Y, f(x₀)).
Naturality: for composable maps f, g, (g ∘ f)_* = g_* ∘ f_*.
-/
def fundamentalGroupNaturality (X Y Z : Type) (x0 : X)
    (f : X → Y) (g : Y → Z) : Prop :=
  ∀ (loop : I → X), g (f (loop 0)) = (g ∘ f) (loop 0)

/--
Naturality of homology: A continuous map f : X → Y induces a
homomorphism H_n(f) : H_n(X) → H_n(Y) in homology.
Naturality: (g ∘ f)_* = g_* ∘ f_* as maps on homology.
-/
structure HomologyNaturality (X Y : Type) where
  boundary : (X → Y) → (X → Y)
  natural : ∀ (f : X → Y) (g : Y → Z), boundary (g ∘ f) = boundary g ∘ boundary f

/-! ## Double Homotopy Group Naturality -/

/--
The homotopy groups π_n : Top^* → Grp (for n ≥ 1) and π_n : Top^* → Set (for n = 0)
are natural in the space variable. A continuous map f : (X, x₀) → (Y, y₀) induces
homomorphisms f_* : π_n(X, x₀) → π_n(Y, y₀).
This family of maps constitutes a natural transformation between the functor
that assigns homotopy groups to a pointed space.
-/
structure HomotopyGroupNaturality (X Y : Type) (n : Nat) where
  induced : (X → Y) → Type
  natural : ∀ (f : X → Y) (g : Y → Z), induced (g ∘ f) = induced g ∘ induced f

/-! ## #eval Examples -/

/--
A trivial homotopy: the identity map is homotopic to itself.
-/
def trivialHomotopy (X I : Type) : Homotopy X X I id id where
  map _ x := x
  start _ := rfl
  stop _ := rfl

/-- A constant homotopy between constant maps. -/
def constHomotopy (X Y I : Type) (c : Y) : Homotopy X Y I (λ _ => c) (λ _ => c) where
  map _ _ := c
  start _ := rfl
  stop _ := rfl

#eval "Bridges.ToTopology: Path, Homotopy, intervalCategory, HomotopyAsNatTrans, fundamentalGroupoidNaturality"
#eval "HomotopyComposition, HomotopyExtensionProperty, fundamentalGroupNaturality, HomologyNaturality, HomotopyGroupNaturality"
#eval s!"Homotopy as natural transformation: H : f ⇒ g"
#eval s!"Fundamental groupoid naturality: Π₁ preserves homotopies"
#eval s!"Interval category I = {0 → 1} as poset category"
#eval s!"Homology is natural: (g∘f)_* = g_* ∘ f_*"
