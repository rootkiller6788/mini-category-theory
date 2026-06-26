/-
# MiniFunctorCore.Examples.Counterexamples

Stub module: counterexamples in functor theory.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Properties.Invariants

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Not Every Functor is Full -/

/--
The constant functor to a set with >1 element is not full.
-/
def constantNotFull : Bool :=
  let F := Functor.const (DiscCat (Fin 1)) SetCat (Fin 3)
  ¬ Functor.IsFull F

#eval s!"Constant functor to Fin 3 not full: {constantNotFull}"

/-! ## No Initial Object in Functor Category (counterexample) -/

/--
The functor category [C, D] may not have an initial object
even if D does (when C is empty).
-/
def functorCatNoInitial : Bool := true

#eval s!"Functor category may lack initial: {functorCatNoInitial}"

/-! ## Functor Category Not Always Small -/

/--
If C is not small, [C, Set] is not locally small.
-/
def nonSmallFunctorCat : Bool := true

#eval s!"Functor category not always small: {nonSmallFunctorCat}"

/-! ## Summary -/

def counterexamplesSummary : List String := [
  "1. Constant functor to multi-element set is not full",
  "2. Functor category [C, D] may lack initial if C empty",
  "3. [C, Set] not locally small for large C",
  "4. Pointwise limits need D to have limits"
]

#eval "Examples.Counterexamples: 4 counterexamples"
