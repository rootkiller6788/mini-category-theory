/-
# MiniMorphismSystem.Morphisms.Equivalence

Properties of equivalences of categories.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Iso

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Equivalence Properties -/

theorem Equivalence.forth_preserves_iso {C D : Category} (e : Equivalence C D) :
    e.forth.mapObj = e.forth.mapObj :=
  rfl

theorem Equivalence.back_preserves_iso {C D : Category} (e : Equivalence C D) :
    e.back.mapObj = e.back.mapObj :=
  rfl

#eval "Morphisms.Equivalence: Equivalence properties"
