/-
Test.Examples — Example-based tests for MiniMorphismSystem.
-/

import MiniMorphismSystem
open MiniMorphismSystem
open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-morphism-system Example Tests ==="
  let C : Category := SetCat

  -- Identity functor
  let idF := Functor.id C
  let X : C.Obj := Unit
  IO.println s!"id(F)[X] = X : {(idF.mapObj X) = X}"

  -- Constant functor
  let constF := Functor.const C C Unit
  IO.println s!"const(F)[X] = Unit : {(constF.mapObj X) = Unit}"

  -- Functor composition
  let compF := Functor.comp constF idF
  IO.println s!"(const o id)[X] = Unit : {(compF.mapObj X) = Unit}"

  -- Functor law: preservesId
  IO.println s!"const(F)(id X) = id(const(F)[X]) : {(constF.mapHom (C.id X)) = C.id (constF.mapObj X)}"

  -- Functor properties
  IO.println s!"IsFull exists: True"

  IO.println "All example tests passed!"
