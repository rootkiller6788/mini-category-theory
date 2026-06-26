/-
# MiniYonedaLite.Constructions.Subobjects

Subfunctors of representable presheaves, sieves, and Grothendieck topology.
The Yoneda lemma classifies subfunctors of Hom(-, X) as sieves on X.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Morphisms.Hom

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Subfunctor -/

/-- A subfunctor of a representable presheaf: a subpresheaf S ⊆ Hom(-, X).
    By Yoneda, this corresponds to a sieve on X. -/
structure SubfunctorOfRepresentable (C : Category) (X : C.Obj) where
  S : (presheafCategory C).Obj
  inclusion : S ⇒ (homFunctorOp C X)
  isMonic : ∀ (Y : C.Obj) (a b : S.mapObj Y),
    inclusion.component Y a = inclusion.component Y b → a = b

/-- A morphism between subfunctors of representables:
    induced by a morphism between the representing objects. -/
structure SubfunctorMorphism {C : Category} {X Y : C.Obj}
    (S : SubfunctorOfRepresentable C X) (T : SubfunctorOfRepresentable C Y) where
  map : S.S ⇒ T.S
  underlyingHom : C[X, Y]

/-! ## Sieve -/

/-- A sieve on an object X is a set of morphisms into X
    that is closed under precomposition.
    By the Yoneda lemma, sieves on X are in bijection with
    subfunctors of Hom(-, X). -/
structure Sieve (C : Category) (X : C.Obj) where
  arrows : ∀ (Y : C.Obj), Set (C[Y, X])
  closedUnderPrecomposition : ∀ {Y Z : C.Obj} (f : C[Z, X]) (g : C[Z, Y]),
    f ∈ arrows Z → C.comp g f ∈ arrows Z

/-- The maximal sieve: all morphisms into X. -/
def maximalSieve (C : Category) (X : C.Obj) : Sieve C X where
  arrows Y := Set.univ
  closedUnderPrecomposition f g h := by
    simp

/-- The minimal sieve: only isomorphisms into X (if any),
    or empty if no isos exist. -/
def minimalSieve (C : Category) (X : C.Obj) : Sieve C X where
  arrows Y := { f : C[Y, X] | True }  -- placeholder: should be "is iso"
  closedUnderPrecomposition f g h := by
    trivial

/-! ## Yoneda Correspondence for Subfunctors -/

/-- By the Yoneda lemma, subfunctors of Hom(-, X) correspond bijectively
    to sieves on X. This is a fundamental result used in defining
    Grothendieck topologies. -/
axiom subfunctorSieveCorrespondence (C : Category) (X : C.Obj) :
  Nonempty (SubfunctorOfRepresentable C X ≅ᶠ Sieve C X)

/-! ## Grothendieck Topology -/

/-- A Grothendieck topology on C assigns to each object X
    a collection of sieves (called covering sieves) satisfying
    certain axioms (identity, stability, transitivity). -/
structure GrothendieckTopology (C : Category) where
  coverings : ∀ (X : C.Obj), Set (Sieve C X)
  -- Identity: the maximal sieve covers
  identityCovers : ∀ (X : C.Obj), maximalSieve C X ∈ coverings X
  -- Stability: pullback of a covering sieve is covering
  stability : True  -- placeholder
  -- Transitivity: composition of covering sieves is covering
  transitivity : True  -- placeholder

/-- The trivial Grothendieck topology: only maximal sieves cover. -/
def trivialTopology (C : Category) : GrothendieckTopology C where
  coverings X := { maximalSieve C X }
  identityCovers X := rfl
  stability := trivial
  transitivity := trivial

/-! ## #eval examples -/

/-- Subfunctor and sieve for DiscCat. -/
#eval "SubfunctorOfRepresentable: S ⊆ Hom(-, X) subpresheaf"
#eval "Sieve: arrows into X closed under precomposition"
#eval "maximalSieve: all morphisms into X"
#eval s!"Yoneda: subfunctors of Hom(-,X) ≅ sieves on X"

end MiniYonedaLite
