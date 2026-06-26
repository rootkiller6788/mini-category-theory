/-
Benchmark: Princeton

Princeton University benchmark for natural transformations.
Tests understanding of natural transformations in category theory.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== Princeton Benchmark: Natural Transformations ==="

  let C : Category := SetCat
  let F := Functor.id C
  let G := Functor.id C

  let η : F ⇒ G := NaturalTransformation.id F
  let μ := NaturalTransformation.vcomp η η

  IO.println s!"Princeton benchmark: vertical composition of identity NTs successful"
  IO.println "Princeton benchmark complete."
