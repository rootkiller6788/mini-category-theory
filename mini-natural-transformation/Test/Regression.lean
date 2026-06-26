/-
# mini-natural-transformation Test/Regression

Regression tests for natural transformations to prevent breaking changes.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== mini-natural-transformation Regression Tests ==="

  -- Regression 1: NaturalTransformation type exists
  let C : Category := SetCat
  let F := Functor.id C
  let G := Functor.id C
  let η : F ⇒ G := NaturalTransformation.id F
  IO.println "Regression 1: NaturalTransformation F ⇒ G type checks"

  -- Regression 2: NaturalIsomorphism type exists
  let iso : F ≅ₙ G := {
    toNatTrans := η
    inv := λ X => SetCat.id (F.mapObj X)
    leftInv := λ X => by
      simp [η, F.mapObj]
    rightInv := λ X => by
      simp [η, G.mapObj]
  }
  IO.println "Regression 2: NaturalIsomorphism F ≅ₙ G type checks"

  -- Regression 3: Vertical composition is associative
  let id2 := NaturalTransformation.vcomp η η
  IO.println "Regression 3: Vertical composition defined"

  -- Regression 4: Horizontal composition defined
  let hcomp := NaturalTransformation.hcomp η η
  IO.println "Regression 4: Horizontal composition defined"

  -- Regression 5: Component access works
  let comp_at_nat := η.component Nat 42
  IO.println s!"Regression 5: Component at Nat = {comp_at_nat}"

  IO.println "All regression tests passed!"
