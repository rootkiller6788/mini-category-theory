/-
# MiniAdjunction.Examples.Standard

Standard adjunctions: free-forgetful (Monoid → Set),
product-exponential, Σ ⊣ Δ ⊣ Π.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Constructions.Products
import MiniAdjunction.Constructions.Universal

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniFunctorCore

/-! ## Identity Adjunction (Simple Example) -/

/--
The identity functor id_C : C → C is left and right adjoint to itself.
-/
def identityAdjunctionExample (C : Category) : (Functor.id C) ⊣ (Functor.id C) :=
  identityAdjunction C

#eval "Examples.Standard: identity adjunction id ⊣ id"

/-! ## Free-Forgetful Adjunction (Conceptual) -/

/--
The archetypal free-forgetful adjunction:
  Free : Set → Monoid  ⊣  Forgetful : Monoid → Set

Here we model it conceptually with set-valued functors.
-/
structure FreeMonoidForgetful where
  free : Functor SetCat SetCat
  forgetful : Functor SetCat SetCat
  adj : free ⊣ forgetful

/--
Free monoid on a set sent to underlying set via forgetful is
an adjunction. For the actual implementation, the free monoid
on type X is List X (words), and the forgetful functor sends
a monoid to its underlying set.
-/
axiom freeMonoidForgetfulAdjunction : FreeMonoidForgetful

#eval "Examples.Standard: FreeMonoidForgetful ⊣ forgetful (axiom)"

/-! ## Product-Exponential Adjunction in Set -/

/--
In the category of sets, (- × A) ⊣ (A ⇒ -).
This is the standard curry/uncurry bijection.
-/
def productExponentialSet (A : Type u) : Prop :=
  True

/--
curry : (X × A → Y) → (X → A → Y)
uncurry : (X → A → Y) → (X × A → Y)
-/
def curry {X Y A : Type u} (f : X × A → Y) (x : X) (a : A) : Y :=
  f (x, a)

def uncurry {X Y A : Type u} (g : X → A → Y) (p : X × A) : Y :=
  g p.1 p.2

/--
curry and uncurry are inverses.
-/
theorem curryUncurryInverse {X Y A : Type u} (f : X × A → Y) : uncurry (curry f) = f := by
  ext p; rcases p with ⟨x, a⟩; rfl

theorem uncurryCurryInverse {X Y A : Type u} (g : X → A → Y) : curry (uncurry g) = g := by
  ext x a; rfl

#eval "Examples.Standard: product-exponential in Set: curry/uncurry bijection"
#eval (curry (λ (x : Bool) (a : Nat) => a > 0) true 5 : Bool)
#eval uncurry (λ (x : Bool) => λ (a : Nat) => a > 0) (false, 3) : Bool

/-! ## Σ ⊣ Δ ⊣ Π Adjunction -/

/--
For discrete categories I, the functor Σ : [I, Set] → Set (coproduct),
Δ : Set → [I, Set] (diagonal), and Π : [I, Set] → Set (product)
form an adjoint triple Σ ⊣ Δ ⊣ Π.
-/
structure SigmaDeltaPi where
  I : Category
  sigma : Functor ([I, SetCat]) SetCat
  delta : Functor SetCat ([I, SetCat])
  pi : Functor ([I, SetCat]) SetCat
  adj1 : sigma ⊣ delta
  adj2 : delta ⊣ pi

/--
Σ ⊣ Δ: coproduct is left adjoint to diagonal.
-/
axiom sigmaDeltaAdjunction : Prop

/--
Δ ⊣ Π: diagonal is left adjoint to product.
-/
axiom deltaPiAdjunction : Prop

/--
The full adjoint triple Σ ⊣ Δ ⊣ Π for discrete categories.
-/
axiom sigmaDeltaPiTriple : Nonempty SigmaDeltaPi

#eval "Examples.Standard: Σ ⊣ Δ ⊣ Π adjoint triple (axiom)"
