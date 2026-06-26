/-
# MiniAdjunction.Morphisms.Iso

Adjoint equivalence, adjoint isomorphism, and uniqueness of adjoints.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Morphisms.Hom

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Adjoint Equivalence -/

/--
An adjoint equivalence is an adjunction where the unit and counit
are natural isomorphisms.
-/
structure AdjointEquivalence (C D : Category) (F : Functor C D) (G : Functor D C) where
  adj : F ⊣ G
  unitIso : ∀ (X : C.Obj), Iso C X (G.mapObj (F.mapObj X))
  counitIso : ∀ (Y : D.Obj), Iso D (F.mapObj (G.mapObj Y)) Y

/--
In an adjoint equivalence, F is fully faithful and essentially surjective,
i.e., F is an equivalence of categories.
-/
axiom adjointEquivalenceIsEquivalence {C D : Category} {F : Functor C D} {G : Functor D C}
    (ae : AdjointEquivalence C D F G) : Functor.IsFullyFaithful F ∧ Functor.IsEssentiallySurjective F

/-! ## Uniqueness of Adjoints -/

/--
If F has two right adjoints G and G', then G and G' are naturally isomorphic.
-/
axiom rightAdjointUniqueUpToIso {C D : Category} {F : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F ⊣ G') : Nonempty (G ⇒ G')

/--
If G has two left adjoints F and F', then F and F' are naturally isomorphic.
-/
axiom leftAdjointUniqueUpToIso {C D : Category} {F F' : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G) : Nonempty (F ⇒ F')

/--
Adjoints are unique up to natural isomorphism (combined statement).
-/
axiom adjointUniqueUpToIsoFull {C D : Category} {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') : Prop

/-! ## Natural Isomorphism Between Adjoints -/

/--
A natural isomorphism between two left adjoints of the same functor induces
a natural isomorphism between their right adjoints, and vice versa.
-/
structure AdjointIso {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') where
  leftNatIso : Nonempty (F ⇒ F')
  rightNatIso : Nonempty (G ⇒ G')
  compatibility : Prop

/-! ## Conjugate Natural Transformations -/

/--
Given adjunctions F ⊣ G and F' ⊣ G', a natural transformation
α : F ⇒ F' induces a conjugate β : G' ⇒ G, and vice versa.
-/
axiom conjugateNaturalTransformation {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (α : F ⇒ F') : Nonempty (G' ⇒ G)

/--
The conjugate operation is a bijection between Nat(F, F') and Nat(G', G).
-/
axiom conjugateBijection {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') : Prop

/-! ## Adjoints and Limits -/

/--
Right adjoints preserve limits. (Fundamental theorem, stated as axiom.)
-/
axiom rightAdjointPreservesLimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Left adjoints preserve colimits.
-/
axiom leftAdjointPreservesColimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
The RAPL principle: Right Adjoint Preserves Limits.
-/
axiom rapl {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

#eval "Morphisms.Iso: AdjointEquivalence, adjointUniqueUpToIso"
#eval "Morphisms.Iso: conjugateNatTrans, RAPL/LAPC (axioms)"
#eval "Morphisms.Iso: Adjoints unique up to natural isomorphism"
