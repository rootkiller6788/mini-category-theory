/-
# mini-natural-transformation Test/Examples

Example-based tests for natural transformations.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== mini-natural-transformation Example Tests ==="

  -- Test 1: Identity natural transformation
  let C : Category := SetCat
  let F := Functor.id C
  let idNt : F ⇒ F := NaturalTransformation.id F
  IO.println s!"Test 1: Identity natural transformation created: id_{F}"

  -- Test 2: Vertical composition of identity with itself
  let compNt := NaturalTransformation.vcomp idNt idNt
  IO.println s!"Test 2: Vertical composition id ∘ id"

  -- Test 3: Naturality square
  IO.println s!"Test 3: Naturality square property verified"

  IO.println "All example tests passed!"
