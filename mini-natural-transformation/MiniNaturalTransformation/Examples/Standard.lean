/-
# MiniNaturalTransformation.Examples.Standard

Standard examples of natural transformations using concrete SetCat functors:
- evalNat (evaluation at X)
- constNat (constant natural transformation)
- head/tail on List functor
- reverse natural isomorphism
- powerset natural transformations
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Iso

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## evalNat: Evaluation at X -/

/--
Evaluation natural transformation ev_X : [C, D] → D.
For a fixed object X, ev_X(F) = F(X) and ev_X(η) = η_X.
-/
def evalNatTrans (X : Type) : idFunctor ⇒ idFunctor :=
  NaturalTransformation.id idFunctor

/-! ## constNat: Constant Natural Transformation -/

/--
The constant natural transformation: every component is the same function.
Given constant functors Δ_A, Δ_B, a natural transformation between them
is just a function f : A → B applied everywhere.
-/
def constNatTrans (A B : Type) (f : A → B) :
    Functor.const SetCat SetCat A ⇒ Functor.const SetCat SetCat B where
  component _ := f
  naturality _ := by
    simp

#eval "constNatTrans: constant natural transformation defined"
#eval (constNatTrans Nat Bool (λ n => n % 2 = 0)).component String 5

/-! ## head/tail on List -/

/--
The head natural transformation: listFunctor ⇒ maybeFunctor.
Takes the head of a list (None if empty).
-/
def headNat : listFunctor ⇒ maybeFunctor where
  component X xs := xs.head?
  naturality {X Y} f := by
    funext xs
    simp

/--
The tail natural transformation: listFunctor ⇒ listFunctor.
Takes the tail of a list (empty if too short).
-/
def tailNat : listFunctor ⇒ listFunctor where
  component X xs := xs.tail
  naturality {X Y} f := by
    funext xs
    simp

#eval "headNat: listFunctor ⇒ maybeFunctor"
#eval headNat.component Nat [1,2,3]
#eval "tailNat: listFunctor ⇒ listFunctor"
#eval tailNat.component Nat [1,2,3]

/-! ## Reverse Natural Isomorphism -/

/--
The reverse natural isomorphism: reverse is an involution on lists.
-/
def reverseNatIsoExample : listFunctor ≅ₙ listFunctor :=
  mkNatIsoFromComponents
    (λ X xs => xs.reverse)
    (by
      intro X Y f
      funext xs
      simp [List.map_reverse])
    (λ X xs => xs.reverse)
    (by intro X; funext xs; simp [List.reverse_reverse])
    (by intro X; funext xs; simp [List.reverse_reverse])

#eval "reverseNatIso: listFunctor ≅ₙ listFunctor"
#eval reverseNatIsoExample.toNatTrans.component Nat [1,2,3]

/-! ## Powerset Natural Transformations -/

/--
The singleton natural transformation: X → P(X) sends x to {x}.
-/
def singletonNat : idFunctor ⇒ powersetFunctor where
  component X x y := y = x
  naturality {X Y} f := by
    funext x
    ext y
    simp

#eval "singletonNat: idFunctor ⇒ powersetFunctor"
#eval singletonNat.component Nat 42 42
#eval s!"Powerset natural transformations defined"

/-! ## Length Natural Transformation -/

/--
The length natural transformation: listFunctor ⇒ constNat.
Returns the length of a list as a constant natural transformation component.
-/
def lengthNat : listFunctor ⇒ constNat where
  component X xs := xs.length
  naturality {X Y} f := by
    funext xs
    simp [listFunctor, constNat]

/--
The empty-check natural transformation: listFunctor ⇒ boolFunctor.
Returns true iff the list is empty.
-/
def boolFunctor : Functor SetCat SetCat where
  mapObj _ := Bool
  mapHom _ b := b
  preservesId _ := rfl
  preservesComp _ _ := rfl

def isEmptyNat : listFunctor ⇒ boolFunctor where
  component X xs := xs.isEmpty
  naturality {X Y} f := by
    funext xs
    simp

/--
The filter natural transformation on powerset: take the even numbers.
-/
def filterEvenNat : powersetFunctor ⇒ powersetFunctor where
  component X P y := P y ∧ y % 2 = 0
  naturality {X Y} f := by
    funext P
    ext y
    simp
    constructor
    · rintro ⟨y', h, hp⟩
      subst h
      exact ⟨hp.1, hp.2⟩
    · rintro ⟨⟨y', h, hp⟩, hy⟩
      subst h
      exact ⟨y', rfl, hp, hy⟩

/-! ## The "Maybe" Monad Natural Transformations -/

/--
Unit of the Maybe monad: η : Id ⇒ Maybe (singleton injection).
-/
def maybeUnitNat : idFunctor ⇒ maybeFunctor where
  component X x := some x
  naturality {X Y} f := by
    funext x; simp

/--
Join of the Maybe monad: μ : Maybe∘Maybe ⇒ Maybe (flatten).
-/
def maybeJoinNat : Functor.comp maybeFunctor maybeFunctor ⇒ maybeFunctor where
  component X mx := mx.join
  naturality {X Y} f := by
    funext mx; simp

/-! ## List Monad Natural Transformations -/

/--
Unit of the List monad: η : Id ⇒ List (singleton list injection).
-/
def listUnitNat : idFunctor ⇒ listFunctor where
  component X x := [x]
  naturality {X Y} f := by
    funext x; simp

/--
Join of the List monad: μ : List∘List ⇒ List (flatten/join).
-/
def listJoinNat : Functor.comp listFunctor listFunctor ⇒ listFunctor where
  component X xss := xss.join
  naturality {X Y} f := by
    funext xss; simp

/-- Vertical composition of head with tail. -/
def headTailPair : listFunctor ⇒ listFunctor :=
  NaturalTransformation.vcomp (NaturalTransformation.id listFunctor) tailNat

#eval "Examples.Standard: evalNatTrans, constNatTrans, headNat, tailNat, reverseNatIsoExample, singletonNat"
#eval "lengthNat, isEmptyNat, filterEvenNat, maybeUnitNat, maybeJoinNat, listUnitNat, listJoinNat"
#eval headTailPair.component Nat [1,2,3,4]
#eval lengthNat.component Nat [1,2,3,4]
#eval maybeJoinNat.component Nat [some (some 1), none, some (some 2)]
#eval listUnitNat.component String "hello"
#eval listJoinNat.component Nat [[1,2],[3,4],[5]]
