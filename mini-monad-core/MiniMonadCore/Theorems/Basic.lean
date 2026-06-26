/-
# MiniMonadCore.Theorems.Basic

Every adjunction F ⊣ G induces a monad G∘F on the domain category.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## Adjunction → Monad -/

def fromAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Monad C where
  T := Functor.comp G F
  η := adj.unit
  μ := {
    component := fun X => G.mapHom (adj.counit.component (F.mapObj X))
    naturality := fun f => by
      simp [adj.leftTriangle, adj.rightTriangle, G.preservesComp, F.preservesComp,
        Functor.comp, C.assoc, D.assoc]
  }
  leftUnit := adj.leftTriangle
  rightUnit := adj.rightTriangle
  associativity := fun X => by
    simp [G.preservesComp, D.assoc, C.assoc]

#eval "Theorems.Basic: Every adjunction induces a monad"
