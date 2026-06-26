/-
# MiniNaturalTransformation.Bridges.ToComputation

Polymorphic functions as natural transformations (parametricity),
and the `map` function as a natural transformation.

In programming language theory, Reynolds' parametricity theorem
states that polymorphic functions ∀X. F X → G X correspond to
natural transformations between the functors F and G.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Parametric Polymorphism = Natural Transformation -/

/--
Reynolds' parametricity: A polymorphic function of type
  ∀ (X : Type), F X → G X
corresponds exactly to a natural transformation F ⇒ G in SetCat.
-/

/--
A polymorphic function: for any type X, a function from F X to G X.
-/
def polymorphicFunction (F G : Type → Type) := ∀ (X : Type), F X → G X

/--
A polymorphic function corresponds to a natural transformation if F and G
are functorial (have map operations).
-/
structure ParametricNatTrans (F G : Functor SetCat SetCat) where
  poly : polymorphicFunction F.mapObj G.mapObj
  parametricity : ∀ (X Y : Type) (f : X → Y) (x : F.mapObj X),
    G.mapHom f (poly X x) = poly Y (F.mapHom f x)

/--
Convert a parametric natural transformation to a standard natural transformation.
-/
def parametricToNatTrans {F G : Functor SetCat SetCat}
    (p : ParametricNatTrans F G) : F ⇒ G where
  component X := p.poly X
  naturality {X Y} f := by
    funext x
    apply p.parametricity X Y f x

/--
Convert a standard natural transformation to a parametric one.
-/
def natTransToParametric {F G : Functor SetCat SetCat}
    (η : F ⇒ G) : ParametricNatTrans F G where
  poly X := η.component X
  parametricity X Y f x := by
    have h := congrFun (η.naturality f) x
    simp at h
    exact h

/-! ## Map as Natural Transformation -/

/--
The `reverse` operation on lists is a natural transformation.
-/
def reversePoly : polymorphicFunction listFunctor.mapObj listFunctor.mapObj :=
  λ X xs => xs.reverse

/--
The parametricity condition for reverse: ∀f, ∀xs,
  List.map f (reverse xs) = reverse (List.map f xs)
This is exactly the naturality of reverse.
-/
theorem reverse_parametricity (X Y : Type) (f : X → Y) (xs : List X) :
    listFunctor.mapHom f (reversePoly X xs) = reversePoly Y (listFunctor.mapHom f xs) := by
  simp [reversePoly, listFunctor, List.map_reverse]

/-! ## Free Theorems -/

/--
The free theorem for a polymorphic function of type ∀X. List X → Option X:
  Option.map f (α_X xs) = α_Y (List.map f xs)
This is exactly the naturality condition for α : List ⇒ Option.
-/
theorem head_freeTheorem (X Y : Type) (f : X → Y) (xs : List X) :
    Option.map f (xs.head?) = (List.map f xs).head? := by
  simp

/-! ## #eval Examples -/

/-- Identity polymorphic function is a natural transformation. -/
def idPoly : polymorphicFunction idFunctor.mapObj idFunctor.mapObj := λ X x => x

/-- The composition of two polymorphic functions corresponds to
vertical composition of natural transformations. -/
def compPoly {F G H : Functor SetCat SetCat}
    (p1 : ParametricNatTrans F G) (p2 : ParametricNatTrans G H) :
    ParametricNatTrans F H :=
  natTransToParametric
    (NaturalTransformation.vcomp
      (parametricToNatTrans p2)
      (parametricToNatTrans p1))

#eval "Bridges.ToComputation: polymorphicFunction, ParametricNatTrans, parametricToNatTrans, reverse_parametricity, head_freeTheorem"
#eval s!"Parametric polymorphism = natural transformations (Reynolds' parametricity)"
#eval s!"map is natural: List.map f ∘ reverse = reverse ∘ List.map f"
#eval reverse_parametricity Nat Bool (λ n => n % 2 = 0) [1,2,3]
#eval s!"Free theorem for head?: Option.map f (head? xs) = head? (List.map f xs)"
