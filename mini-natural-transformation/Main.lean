import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniNaturalTransformation v0.1.0"
  IO.println "  Natural Transformations Between Functors"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  NaturalTransformation F G: component + naturality square"
  IO.println s!"  Notation: F ⇒ G"
  IO.println s!"  Vertical composition η ∘ᵥ μ: stacking transformations"
  IO.println s!"  Horizontal composition ('whiskering'): pre/post-composition with functors"
  IO.println s!"  NaturalTransformation.id: identity natural transformation"
  IO.println s!"  Functor category [C, D]: objects are functors, morphisms are natural transformations"
  IO.println s!"  Shared functors: listFunctor, maybeFunctor, powersetFunctor, idFunctor, constNat"
  IO.println ""
  IO.println "  Depends on: mini-category-core, mini-morphism-system"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
