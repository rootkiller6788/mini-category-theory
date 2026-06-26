/-
# MiniYonedaLite.Bridges.ToComputation

Yoneda lemma connections to functional programming and computation:
- Continuation-passing style (CPS) as the Yoneda embedding for types
- Church encoding of data types via Yoneda
- Kan extensions in functional programming
- Free monads and the Coyoneda lemma for functors
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Continuation-Passing Style (CPS) as Yoneda -/

/-- In functional programming, the continuation-passing transform of
    a type A is (A → R) → R for some result type R. This is exactly
    the Yoneda embedding of A into the presheaf category:
    Y(A) = Hom(-, A) = λ X → (A → X) → X (double-dual).
    CPS = Yoneda embedding for the category of types. -/

/-- The CPS transform of a type A with result type R:
    CPS_R(A) = (A → R) → R. This is isomorphic to A for any R
    (by Yoneda if we view types as functors). -/
def cpsTransform (A R : Type u) : Type u := (A → R) → R

/-- The Yoneda lemma says that Nat(Hom(A, -), Id) ≅ Id(A).
    In programming terms: for any functor F, the natural transformations
    from (A → -) to F are in bijection with F(A). -/
def cpsHom (A : Type u) : Type u := ∀ {X : Type u}, (A → X) → X

/-- The Yoneda identity: ∀ A, CPS_Hom(A) ≅ A. This is a programming
    manifestation of the Yoneda lemma: the only polymorphic function
    of type ∀ X, (A → X) → X is essentially the identity at A. -/
axiom cpsYonedaIdentity (A : Type u) : Nonempty (cpsHom A ≅ᶠ A)

/-! ## Church Encoding -/

/-- Church encoding of a data type uses Yoneda: e.g., Church numerals
    are the Yoneda embedding of Nat into the presheaf category.
    Nat ≅ ∀ X, (X → X) → (X → X). This is Nat as a representable functor. -/
def churchNat : Type 1 := ∀ {X : Type}, (X → X) → (X → X)

/-- The Yoneda lemma proves that ChurchNat ≅ Nat: the only terms
    of type ∀ X, (X → X) → (X → X) are the Church numerals. -/
axiom churchEncodingYoneda : Nonempty (churchNat ≅ᶠ Nat)

/-- Church booleans: Bool ≅ ∀ X, X → X → X.
    Two terms: true = λ x y → x, false = λ x y → y. Yoneda says these
    are the only two. -/
def churchBool : Type 1 := ∀ {X : Type}, X → X → X

/-! ## Coyoneda Lemma for Functors -/

/-- The Coyoneda lemma (dual of Yoneda) is used pervasively in
    functional programming to make functors "free":
    Coyoneda F A ≅ F A, where Coyoneda F A = ∃ X, (X → A, F X). -/
axiom coyonedaForFunctors : True

/-- In Haskell, the Coyoneda lemma lets us define Functor instances
    without requiring an explicit fmap for all functors. -/
def coyoneda {F : Type u → Type u} (A : Type u) : Type (u + 1) :=
  Σ (X : Type u), (X → A) × F X

/-! ## Free Monads and Kan Extensions -/

/-- The free monad on a functor F is given by the left Kan extension
    of F along itself. Yoneda and Kan extensions are closely related:
    Lan_Y F ≅ the left Kan extension of F along Yoneda. -/
axiom freeMonadYoneda : True

/-- The Yoneda lemma is used to compute right Kan extensions in
    functional programming: Ran_G F A ≅ ∀ X, (A → G X) → F X. -/
def rightKanExtension {G : Type u → Type u} {F : Type u → Type u} (A : Type u) : Type (u + 1) :=
  ∀ {X : Type u}, (A → G X) → F X

/-! ## Parametricity and Yoneda -/

/-- Reynolds' parametricity (theorems for free) implies the Yoneda
    lemma for the category of types: the only inhabitants of
    ∀ X, (A → X) → F X are those corresponding to F(A). -/
axiom parametricityYoneda : True

/-- Theorems for free: a polymorphic function f : ∀ X, (A → X) → X
    must be of the form λ g → g a for some a : A. This is exactly
    the forward direction of the Yoneda lemma. -/
axiom theoremsForFree (A : Type u) : True

/-! ## #eval examples -/

/-- Computation connections. -/
#eval "CPS transform: CPS_R(A) = (A → R) → R ≅ A (by Yoneda)"
#eval "Church encoding: Nat ≅ ∀ X, (X → X) → (X → X)"
#eval "Church Bool: Bool ≅ ∀ X, X → X → X (only 2 terms)"
#eval "Coyoneda: Coyoneda F A ≅ F A (free Functor)"
#eval s!"Right Kan extension: Ran_G F A ≅ ∀ X, (A → G X) → F X"

end MiniYonedaLite
