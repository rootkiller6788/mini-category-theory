/-
# MiniFunctorCore.Morphisms.Equivalence

Stub module for equivalence-related structures.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Equivalence of Functor Categories -/

/--
Two functor categories are equivalent if there exists an equivalence
of categories between them.
-/
structure FunctorCategoryEquivalence (C D E F : Category) where
  L : Functor ([C, D]) ([E, F])
  R : Functor ([E, F]) ([C, D])
  eq : FunctorEquivalence ([C, D]) ([E, F]) := by
    exact {
      F := L
      G := R
      unitIso := NaturalIsomorphism.id (Functor.comp R L)
      counitIso := NaturalIsomorphism.id (Functor.comp L R)
    }

/-! ## Stub for future work -/

#eval "Morphisms.Equivalence: stub — FunctorCategoryEquivalence"
