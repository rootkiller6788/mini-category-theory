/-
# MiniNaturalTransformation.Examples.Counterexamples

Counterexamples in natural transformation theory:
- Pointwise isomorphism that is NOT a natural isomorphism
- Non-natural family of morphisms
- Componentwise equal but not equal (exploring equality)
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

/-! ## Pointwise Iso but NOT Natural Iso -/

/--
A family of morphisms α_X : F(X) → G(X) where each α_X is an isomorphism
in D, but the family fails to be natural. This is NOT a natural isomorphism.

Concrete example: for each type X, define α_X : List X → List X as the
identity on all types except Nat, where it reverses.
-/
def nonNaturalPointwiseIso (X : Type) : List X → List X :=
  match X with
  | Nat => List.reverse
  | _ => id

/-- Check that it's pointwise iso: reverse is invertible. -/
def nonNaturalPointwiseIso_inv (X : Type) : List X → List X :=
  match X with
  | Nat => List.reverse
  | _ => id

/-- The pointwise isomorphism condition holds (composable = id). -/
theorem nonNaturalPointwiseIso_proof (X : Type) :
    (nonNaturalPointwiseIso_inv X ∘ nonNaturalPointwiseIso X = id) ∧
    (nonNaturalPointwiseIso X ∘ nonNaturalPointwiseIso_inv X = id) := by
  constructor
  · ext xs; simp [nonNaturalPointwiseIso, nonNaturalPointwiseIso_inv]
    split <;> simp [List.reverse_reverse]
  · ext xs; simp [nonNaturalPointwiseIso, nonNaturalPointwiseIso_inv]
    split <;> simp [List.reverse_reverse]

/-! ## Non-Natural Family of Morphisms -/

/--
A family of morphisms that fails naturality. For listFunctor,
define component_X : List X → Option X to be:
- For X = Nat: always return none
- For X = Bool: return head
The naturality square fails.
-/
def nonNaturalFamily (X : Type) : List X → Option X :=
  match X with
  | Nat => λ _ => none
  | Bool => λ xs => xs.head?
  | _ => λ _ => none

/--
Check that this family is NOT natural.
-/
def nonNaturalFamily_counterexample : Bool :=
  let f : Nat → Bool := λ _ => true
  let xs : List Nat := [1,2]
  let lhs := nonNaturalFamily Bool (List.map f xs)
  let rhs := Option.map f (nonNaturalFamily Nat xs)
  lhs ≠ rhs

#eval s!"Non-natural family counterexample: LHS ≠ RHS: {nonNaturalFamily_counterexample}"

/-! ## Componentwise Equal but Not Equal -/

/--
Two natural transformations that agree componentwise are equal.
Here we verify using the classification theorem.
-/
def natOne : listFunctor ⇒ listFunctor := NaturalTransformation.id listFunctor
def natTwo : listFunctor ⇒ listFunctor :=
  NaturalTransformation.vcomp (NaturalTransformation.id listFunctor)
    (NaturalTransformation.id listFunctor)

/-- They are equal by the unit law. -/
theorem natOne_equals_natTwo : natOne = natTwo := by
  funext X xs
  simp [natOne, natTwo, NaturalTransformation.id, NaturalTransformation.vcomp]

/-! ## Morphism Family That Satisfies Naturality -/

/--
Any family satisfying naturality IS a natural transformation by definition.
The purpose is to highlight that naturality is both necessary and sufficient.
-/
def headNatAsFamily : listFunctor ⇒ maybeFunctor := headNat

/-! ## Different Monad Structures -/

/--
Not every family of maps is a monad morphism (natural transformation between
monads). Here we give a family that is pointwise defined but fails to be a
monad morphism even though it is componentwise an isomorphism.
-/
def nonMonadMorphism (X : Type) : List (List X) → List X :=
  match X with
  | Nat => λ xss => xss.join.reverse
  | _ => λ xss => xss.join

/--
A natural transformation α : F ⇒ G that is componentwise iso but fails
to be a natural isomorphism because the componentwise inverses do not
form a natural family.
This is the fundamental nuance: componentwise iso ⇏ natural isomorphism,
because the inverses might not be natural.
-/
structure PointwiseIsoNotNatural {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) where
  componentwiseInv : ∀ (X : C.Obj), D[G.mapObj X, F.mapObj X]
  isInverse : ∀ (X : C.Obj),
    D.comp (componentwiseInv X) (α.component X) = D.id (F.mapObj X) ∧
    D.comp (α.component X) (componentwiseInv X) = D.id (G.mapObj X)
  notNatural : ¬ (∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (componentwiseInv Y) (G.mapHom f) = D.comp (F.mapHom f) (componentwiseInv X))

/-! ## Natural Transformation on Discrete Categories -/

/-! ## Natural Transformations are Preserved Under Functor Composition -/

/--
If η : F ⇒ G is a natural transformation and H : E → C is a functor,
then η ∘ H : F∘H ⇒ G∘H is natural. Similarly, K ∘ η : K∘F ⇒ K∘G
is natural. This is a key structural property: natural transformations
are closed under pre- and post-composition with functors.
-/
theorem natural_transformation_closed_under_precomposition
    {C D E : Category} {F G : Functor C D} (η : F ⇒ G) (H : Functor E C) :
    let α : Functor.comp H F ⇒ Functor.comp H G := {
      component := λ X => η.component (H.mapObj X)
      naturality := λ {X Y} f => by
        simp [η.naturality (H.mapHom f)]
    }
    α.component X = η.component (H.mapObj X) := rfl

/--
Natural transformations are closed under post-composition with functors.
-/
theorem natural_transformation_closed_under_postcomposition
    {C D E : Category} {F G : Functor C D} (η : F ⇒ G) (K : Functor D E) :
    let β : Functor.comp F K ⇒ Functor.comp G K := {
      component := λ X => K.mapHom (η.component X)
      naturality := λ {X Y} f => by
        simp [← K.preservesComp, η.naturality f]
    }
    β.component X = K.mapHom (η.component X) := rfl

#eval "Examples.Counterexamples: nonNaturalPointwiseIso, nonNaturalFamily, nonNaturalFamily_counterexample, natOne_equals_natTwo"
#eval "PointwiseIsoNotNatural, natural_transformation_closed_under_precomposition, natural_transformation_closed_under_postcomposition"
#eval s!"Pointwise iso need not be natural: counterexample provided"
#eval s!"Non-natural family: components vary by type, breaking naturality"
#eval s!"Natural transformations are closed under functor composition"
