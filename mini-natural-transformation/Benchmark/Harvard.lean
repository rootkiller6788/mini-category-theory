/-
Benchmark: Harvard

Harvard University benchmark for natural transformations.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== Harvard Benchmark: Natural Transformations ==="

  let C : Category := SetCat
  let F := Functor.id C
  let G := Functor.id C

  let η : F ⇒ G := NaturalTransformation.id F
  let μ := NaturalTransformation.vcomp η η

  IO.println s!"Harvard benchmark: NT vcomp successful"
  IO.println "Harvard benchmark complete."
