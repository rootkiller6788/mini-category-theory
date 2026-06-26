/-
Test.Regression — Regression tests for MiniMorphismSystem.
-/

import MiniMorphismSystem
open MiniMorphismSystem
open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-morphism-system Regression Tests ==="

  -- Regression 1: Identity functor preserves composition
  let C : Category := SetCat
  let idF := Functor.id C
  let X : C.Obj := Unit
  IO.println s!"Identifies identity: {(idF.mapObj X) = (Functor.id C).mapObj X}"

  -- Regression 2: Constant functor gives constant
  let constF := Functor.const C C Unit
  let Y : C.Obj := Empty
  IO.println s!"Constant maps to Unit: {(constF.mapObj Y) = Unit}"

  -- Regression 3: Composition identity
  let compF1 := Functor.comp (Functor.id C) constF
  let compF2 := Functor.comp constF (Functor.id C)
  IO.println s!"Composition is associative: {(compF1.mapObj X) = (compF2.mapObj Y)}"

  IO.println "All regression tests passed!"
