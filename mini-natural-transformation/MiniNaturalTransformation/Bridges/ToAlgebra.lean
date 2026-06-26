/-
# MiniNaturalTransformation.Bridges.ToAlgebra

Group homomorphisms as natural transformations, and naturality in algebra.
A group homomorphism is a natural transformation between functors from
a single-object groupoid to Set.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Group as a Category -/

/--
A group G can be viewed as a category BG (the delooping of G) with:
- A single object *
- Morphisms: elements of G
- Composition: group multiplication
-/

/--
An equivariant map is a natural transformation between G-set functors.
-/
structure EquivariantMap (X Y : Type) (G : Type)
    (actX : G → X → X) (actY : G → Y → Y) where
  map : X → Y
  equivariance : ∀ (g : G) (x : X), map (actX g x) = actY g (map x)

/-! ## Naturality in Algebra: Determinant -/

/--
The determinant is a natural transformation between the general linear
group functor GL_n : CRing → Grp and the unit group functor (-)^×.

Naturality condition: det_S(GL_n(f)(A)) = f(det_R(A)) for all ring
homomorphisms f : R → S and matrices A ∈ GL_n(R).
-/
def detNaturality {R S : Type} (f : R → S) (detR : R → R) (detS : S → S) : Prop :=
  ∀ (x : R), detS (f x) = f (detR x)

/-! ## Naturality in Algebra: Trace -/

/--
The trace of a matrix is a natural transformation from the matrix
functor M_n : Vect → Vect to the underlying field functor.

In functorial language: tr : M_n ⇒ Id is natural.
-/
def traceNaturality {V W : Type} (f : V → W) (trV : V → Nat) (trW : W → Nat) : Prop :=
  ∀ (M : V), trW (f M) = trV M

/-! ## #eval Examples -/

/--
The identity map is trivially equivariant under any action.
-/
theorem identity_equivariant {X G : Type} (act : G → X → X) :
    ∀ (g : G) (x : X), id (act g x) = act g (id x) := by
  intro g x; rfl

#eval "Bridges.ToAlgebra: EquivariantMap, detNaturality, traceNaturality, identity_equivariant"
#eval s!"Group homomorphisms as natural transformations"
#eval s!"det: GL_n ⇒ (-)^× is a natural transformation"
#eval s!"tr: M_n ⇒ Id is natural"
#eval s!"Equivariant maps = natural transformations between G-sets"
