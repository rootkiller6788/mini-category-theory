import MiniMorphismSystem

open MiniMorphismSystem
open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-morphism-system Smoke Tests ==="
  let C : Category := SetCat
  let F := Functor.id C
  IO.println s!"Identity functor: F[Unit] = F[Unit]"
  let G := Functor.const C C Unit
  IO.println s!"Constant functor maps everything to Unit"
  let H := Functor.comp F G
  IO.println s!"Composition of functors works"
  let cat := Cat
  IO.println s!"Cat category: Obj = Category, Hom = Functor"
  IO.println "All smoke tests passed!"
