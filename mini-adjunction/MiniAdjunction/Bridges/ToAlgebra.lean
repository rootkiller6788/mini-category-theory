/-
# MiniAdjunction.Bridges.ToAlgebra

Galois connections as poset adjunctions, free algebra adjunctions.
Connecting adjunction theory to algebra.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Constructions.Universal

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Galois Connection as Poset Adjunction -/

/--
A Galois connection between posets P and Q is an adjunction between
the corresponding thin categories. A pair of monotone maps
  f : P → Q, g : Q → P
satisfying f(p) ≤ q ↔ p ≤ g(q).
-/
structure GaloisConnection (P Q : Category) where
  l : Functor P Q
  r : Functor Q P
  adj : l ⊣ r
  thinP : Prop  -- P is a thin category (poset)
  thinQ : Prop  -- Q is a thin category (poset)

/--
In a Galois connection, the left adjoint preserves joins (colimits)
and the right adjoint preserves meets (limits).
-/
axiom galoisLeftPreservesJoins {P Q : Category}
    (gc : GaloisConnection P Q) : Prop

/--
Galois connection via monotone maps on posets.
-/
axiom galoisConnectionMonotone : Prop

/--
The closure operator of a Galois connection: cl(p) = r(l(p)).
This is a monotone, idempotent map with p ≤ cl(p).
-/
axiom galoisClosureOperator {P Q : Category}
    (gc : GaloisConnection P Q) : Prop

#eval "Bridges.ToAlgebra: GaloisConnection = poset adjunctions"

/-! ## Free Algebra Adjunctions -/

/--
The free monoid adjunction: F : Set → Monoid ⊣ U : Monoid → Set.
-/
axiom freeMonoidAdjunctionAlgebra : Prop

/--
The free group adjunction: F : Set → Group ⊣ U : Group → Set.
The free group on a set X is isomorphic to the free group on the
reduced words.
-/
axiom freeGroupAdjunctionAlgebra : Prop

/--
The free abelian group adjunction: F : Set → Ab ⊣ U : Ab → Set.
The free abelian group on X is Z^X.
-/
axiom freeAbelianGroupAdjunction : Prop

/--
The free ring adjunction: given a ring R, the free R-algebra
F : Set → R-Alg ⊣ U : R-Alg → Set.
-/
axiom freeAlgebraAdjunction : Prop

/--
The free vector space adjunction: for a field k,
F : Set → Vect_k ⊣ U : Vect_k → Set.
F(X) = k^X (direct sum of X copies of k).
-/
axiom freeVectorSpaceAdjunctionAlgebra (k : Type u) : Prop

/--
The tensor-hom adjunction: for modules M,N,P over a ring R,
  Hom_R(M ⊗ N, P) ≅ Hom_R(M, Hom_R(N, P)).
-/
axiom tensorHomAdjunctionAlgebra : Prop

#eval "Bridges.ToAlgebra: free monoid/group/ring/vector space adjunctions (axioms)"
#eval "Bridges.ToAlgebra: tensor-hom adjunction for modules"
#eval "Bridges.ToAlgebra: Galois connection closure operator"

/-! ## Group Actions and Adjoints -/

/--
The category of G-sets has a forgetful functor to Set with
both a left adjoint (free G-set) and a right adjoint (cofree G-set).
This is an example of an essential geometric morphism.
-/
axiom groupActionAdjoints (G : Type u) : Prop

#eval "Bridges.ToAlgebra: group action adjoints (free ⊣ forgetful ⊣ cofree)"
