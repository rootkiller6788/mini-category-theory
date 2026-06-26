/-
Benchmark: Oxford Part C

University of Oxford Part C Mathematics benchmark for natural transformations.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== Oxford Part C Benchmark: Natural Transformations ==="

  let C : Category := SetCat
  let F := Functor.id C
  let G := Functor.id C

  let η : F ⇒ G := NaturalTransformation.id F
  let μ := NaturalTransformation.vcomp η η

  IO.println s!"Oxford Part C benchmark: NT definitions verified"
  IO.println "Oxford Part C benchmark complete."
