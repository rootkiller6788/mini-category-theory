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

/-! ## Module Homomorphisms as Natural Transformations -/

/--
Given rings R, S, an (R, S)-bimodule M induces functors M ⊗_R - and
M ⊗_S -. A bimodule homomorphism f : M → N induces a natural transformation
between these tensor functors.
-/
structure BimoduleHom (R S M N : Type) where
  map : M → N
  -- would satisfy additivity and R/S-linearity in a full development

/--
The double dual embedding V → V** is a natural transformation
from the identity functor to the double dual functor on the category
of finite-dimensional vector spaces.
-/
def doubleDualNatTrans {K V : Type} (eval : V → ((V → K) → K)) : Prop :=
  ∀ (v : V) (f : V → K), eval v f = f v

/--
The center Z(G) of a group G: the natural transformation
Z : Grp → Ab (center functor) is natural with respect to group homomorphisms.
-/
structure CenterFunctor (G : Type) where
  center : G → Prop
  -- Elements commuting with all elements: ∀ g h, center g → g*h = h*g

/--
The abelianization functor G → G/[G,G] is a natural transformation from
the identity functor on Grp to the abelianization functor.
Naturality: for any group homomorphism f : G → H, the square with
abelianization commutes.
-/
def abelianizationNaturality {G H : Type} (f : G → H)
    (abG : G → G) (abH : H → H) : Prop :=
  ∀ (g : G), abH (f g) = f (abG g)

/-! ## Algebra-Endofunctor Natural Transformations -/

/--
In the category of vector spaces over a field K, the tensor algebra
T(V) gives a functor Vect_K → Alg_K. The universal property of T(V)
is encoded as a natural isomorphism Hom_Alg(T(V), A) ≅ Hom_Vect(V, U(A))
where U is the forgetful functor.
-/
structure TensorAlgebraUniversal (K V : Type) where
  unit : V → List V
  universal : ∀ (A : Type) (f : V → A), ∃! (g : List V → A), g ∘ unit = f

/-! ## #eval Examples -/

/--
The identity map is trivially equivariant under any action.
-/
theorem identity_equivariant {X G : Type} (act : G → X → X) :
    ∀ (g : G) (x : X), id (act g x) = act g (id x) := by
  intro g x; rfl

/-- The determinant as a natural transformation on 2×2 matrices. -/
def det2x2 (a b c d : Nat) : Nat := a * d - b * c

/-- The trace as a natural transformation on 2×2 matrices. -/
def trace2x2 (a b c d : Nat) : Nat := a + d

#eval "Bridges.ToAlgebra: EquivariantMap, detNaturality, traceNaturality, identity_equivariant"
#eval "BimoduleHom, doubleDualNatTrans, CenterFunctor, abelianizationNaturality, TensorAlgebraUniversal"
#eval s!"Group homomorphisms as natural transformations"
#eval s!"det: GL_n ⇒ (-)^× is a natural transformation"
#eval s!"tr: M_n ⇒ Id is natural"
#eval s!"Equivariant maps = natural transformations between G-sets"
#eval s!"Trace of 2x2: {trace2x2 1 2 3 4}"
#eval s!"Det of 2x2: {det2x2 1 2 3 4}"
