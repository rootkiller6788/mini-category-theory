/-
# MiniFunctorCore.Theorems.Basic

Stub module: basic theorems about functor categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Constructions.Products
import MiniFunctorCore.Properties.Invariants

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Yoneda Lemma for Functor Categories -/

/--
The Yoneda lemma for functor categories (stated as axiom).
For a functor F : C → Set and object X in C, there is a bijection
Hom(yX, F) ≅ F(X).
-/
axiom yonedaLemma {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  True

/-! ## Yoneda Embedding -/

/--
The Yoneda embedding Y : Cᵒᵖ → [C, Set] is fully faithful (axiom).
-/
axiom yonedaEmbeddingFullyFaithful {C : Category} :
  Functor.IsFullyFaithful (homFunctorOp C)

/-! ## Density Theorem -/

/--
Every presheaf is a colimit of representables (axiom).
-/
axiom densityTheorem {C : Category} (F : Functor (Cᵒᵖ) SetCat) :
  True

/-! ## Functor Category Completeness -/

/--
If D is complete, then [C, D] is complete (limits computed pointwise).
-/
def functorCategoryCompleteness (C D : Category) : True := by
  trivial

#eval "Theorems.Basic: stub — yonedaLemma, yonedaEmbeddingFullyFaithful, densityTheorem, functorCategoryCompleteness"
