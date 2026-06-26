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

/-! ## Natural Transformation in Functional Programming -/

/--
The `flatten` operation (join) for nested monads is a natural transformation.
For the List monad: join : List∘List ⇒ List.
Naturality: List.map f ∘ join = join ∘ (List.map ∘ List.map f)
-/
def joinPolymorphic : polymorphicFunction (Functor.comp listFunctor listFunctor).mapObj listFunctor.mapObj :=
  λ X xss => xss.join

/--
The `pure` operation of an applicative functor is a natural transformation
from the identity functor to the applicative functor.
For List: pure(x) = [x]
Naturality: List.map f ∘ pure = pure ∘ f
-/
theorem pure_naturality (X Y : Type) (f : X → Y) (x : X) :
    listFunctor.mapHom f ([x] : List X) = ([f x] : List Y) := by
  simp

/--
The `bind` (>>=) operation for monads: for the List monad,
bind : List X → (X → List Y) → List Y.
This corresponds to a natural transformation in a specific sense.
-/
def listBind (X Y : Type) (xs : List X) (f : X → List Y) : List Y :=
  xs.bind f

/--
Naturality of bind: for f : X → Y and g : Y → List Z,
  bind (map f xs) g = bind xs (g ∘ f)
-/
theorem bind_naturality (X Y Z : Type) (f : X → Y) (g : Y → List Z) (xs : List X) :
    listBind Y Z (listFunctor.mapHom f xs) g = listBind X Z xs (g ∘ f) := by
  simp [listBind, listFunctor, List.bind_map]

/-- Filter as a natural transformation on powerset. -/
def filterPoly (p : ∀ {X : Type}, X → Bool) :
    polymorphicFunction powersetFunctor.mapObj powersetFunctor.mapObj :=
  λ X P y => P y ∧ p y

/--
Naturality of filter: for f : X → Y,
  ∃ image P → filter in image = image of filter
-/
theorem filter_naturality (X Y : Type) (f : X → Y) (p : Y → Bool) (P : X → Prop) (y : Y) :
    (∃ x, f x = y ∧ P x ∧ p (f x)) ↔ (∃ x, f x = y ∧ P x) ∧ p y := by
  constructor
  · rintro ⟨x, hx, hP, hp⟩
    subst hx
    exact ⟨⟨x, rfl, hP⟩, hp⟩
  · rintro ⟨⟨x, hx, hP⟩, hp⟩
    subst hx
    exact ⟨x, rfl, hP, hp⟩

/-! ## Distributive Law as Natural Transformation -/

/--
A distributive law of a monad T over a monad S is a natural transformation
λ : T∘S ⇒ S∘T satisfying certain axioms. For example, the distributive law
Maybe over List: λ_X : Maybe(List X) → List(Maybe X)
  none ↦ [none]
  some [] ↦ []
  some (x::xs) ↦ some x :: λ_X(some xs)
-/
def maybeListDistLaw (X : Type) : Option (List X) → List (Option X)
  | none => [none]
  | some [] => []
  | some (x :: xs) => some x :: maybeListDistLaw X (some xs)

/--
The naturality of the distributive law:
  List.map (Option.map f) ∘ λ_X = λ_Y ∘ Option.map (List.map f)
-/
theorem distLaw_naturality (X Y : Type) (f : X → Y) (mxl : Option (List X)) :
    listFunctor.mapHom (Option.map f) (maybeListDistLaw X mxl) =
    maybeListDistLaw Y (Option.map (List.map f) mxl) := by
  induction' mxl with xs
  · simp [maybeListDistLaw]
  · induction' xs with x xs ih
    · simp [maybeListDistLaw]
    · simp [maybeListDistLaw, ih]

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

/-- The natural transformation for the `fmap` of Functor in Haskell. -/
def fmapPoly (F : Functor SetCat SetCat) :
    polymorphicFunction (Functor.comp idFunctor (Functor.const SetCat SetCat (F.mapObj))).mapObj
      F.mapObj :=
  λ X f => F.mapHom f

#eval "Bridges.ToComputation: polymorphicFunction, ParametricNatTrans, parametricToNatTrans, reverse_parametricity, head_freeTheorem"
#eval "joinPolymorphic, pure_naturality, listBind, bind_naturality, filterPoly, filter_naturality"
#eval "maybeListDistLaw, distLaw_naturality, fmapPoly"
#eval s!"Parametric polymorphism = natural transformations (Reynolds' parametricity)"
#eval s!"map is natural: List.map f ∘ reverse = reverse ∘ List.map f"
#eval reverse_parametricity Nat Bool (λ n => n % 2 = 0) [1,2,3]
#eval s!"Free theorem for head?: Option.map f (head? xs) = head? (List.map f xs)"
#eval s!"Distributive law: Maybe ∘ List ⇒ List ∘ Maybe"
#eval maybeListDistLaw Nat (some [1,2,3])
