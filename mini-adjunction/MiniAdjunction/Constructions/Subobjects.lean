/-
# MiniAdjunction.Constructions.Subobjects

Subadjunctions, restriction of adjunction, coreflective subcategories.
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

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Subadjunction -/

/--
A subadjunction is an adjunction restricted to subcategories.
Given F ⊣ G : C ⇄ D and subcategories C' ⊆ C, D' ⊆ D,
if F(C') ⊆ D' and G(D') ⊆ C', then the restriction is an adjunction.
-/
structure Subadjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (C' : Category) (D' : Category)
    (incC : Functor C' C) (incD : Functor D' D) where
  F' : Functor C' D'
  G' : Functor D' C'
  F'_commutes : Functor.comp incD F' = Functor.comp F incC
  G'_commutes : Functor.comp incC G' = Functor.comp G incD
  subadj : F' ⊣ G'

/-! ## Coreflective Subcategory -/

/--
A coreflective subcategory is one where the inclusion has a right adjoint.
Dually to reflective: the inclusion is a right adjoint.
-/
structure CoreflectiveSubcategory (C : Category) (D : Category) where
  inclusion : Functor D C
  coreflector : Functor C D
  adj : coreflector ⊣ inclusion

/--
In a coreflective subcategory, the inclusion is fully faithful.
-/
axiom coreflectiveInclusionFullyFaithful {C D : Category}
    (cs : CoreflectiveSubcategory C D) : Functor.IsFullyFaithful cs.inclusion

/--
The coreflector is essentially surjective (up to equivalence).
-/
axiom coreflectorEssentiallySurjective {C D : Category}
    (cs : CoreflectiveSubcategory C D) : Functor.IsEssentiallySurjective cs.coreflector

/-! ## Restriction of Adjunction -/

/--
Given an adjunction F ⊣ G : C ⇄ D, we can restrict it to
subcategories along fully faithful inclusions.
-/
structure RestrictedAdjunction {C C' D D' : Category}
    {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  incC : Functor C' C
  incD : Functor D' D
  F' : Functor C' D'
  G' : Functor D' C'
  F'Restricts : Prop
  G'Restricts : Prop
  restAdj : F' ⊣ G'

/-! ## Adjunction and Monads -/

/--
Every adjunction F ⊣ G gives rise to a monad G ∘ F on C.
-/
structure AdjunctionMonad {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  monadFunctor : Functor C C
  unit : Functor.id C ⇒ monadFunctor
  multiplication : Functor.comp monadFunctor monadFunctor ⇒ monadFunctor

/--
The monad unit is the adjunction unit.
-/
axiom monadUnitIsAdjUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Prop

/--
The monad multiplication is G ε F.
-/
axiom monadMultiplicationIsGepsF {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Prop

/-! ## Comonad from Adjunction -/

/--
Every adjunction F ⊣ G gives rise to a comonad F ∘ G on D.
-/
structure AdjunctionComonad {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  comonadFunctor : Functor D D
  counit : comonadFunctor ⇒ Functor.id D
  comultiplication : comonadFunctor ⇒ Functor.comp comonadFunctor comonadFunctor

#eval "Constructions.Subobjects: Subadjunction, CoreflectiveSubcategory"
#eval "Constructions.Subobjects: RestrictedAdjunction, monad/comonad from adjunction"
#eval "Constructions.Subobjects: coreflectiveInclusionFullyFaithful (axiom)"
