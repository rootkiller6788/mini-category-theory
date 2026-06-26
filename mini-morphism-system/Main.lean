import MiniMorphismSystem

open MiniMorphismSystem
open MiniCategoryCore

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniMorphismSystem v0.1.0"
  IO.println "  Functor, Full/Faithful, Equivalence of Categories"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Functor C D: mapObj, mapHom, preservesId, preservesComp"
  IO.println s!"  Functor.const: constant functor at a fixed object"
  IO.println s!"  Notation: F[X] for object map, F⟦f⟧ for morphism map"
  IO.println s!"  Functor.id: identity functor"
  IO.println s!"  Functor.comp: composition of functors"
  IO.println s!"  Full / Faithful / FullyFaithful: properties of functors"
  IO.println s!"  EssentiallySurjective: every target object is isomorphic to F[X]"
  IO.println s!"  Equivalence of categories: fully faithful + essentially surjective"
  IO.println ""
  IO.println "  Depends on: mini-category-core"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
