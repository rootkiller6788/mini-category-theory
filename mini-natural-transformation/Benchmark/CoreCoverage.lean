/-
Benchmark: CoreCoverage

Verifies that all core types and operations compile and are accessible.
-/

import MiniNaturalTransformation

open MiniNaturalTransformation
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "=== mini-natural-transformation Core Coverage Benchmark ==="

  let C : Category := SetCat
  let F := Functor.id C
  let G := Functor.id C

  -- NaturalTransformation
  let η : F ⇒ G := NaturalTransformation.id F
  let μ : F ⇒ G := NaturalTransformation.vcomp η η
  IO.println s!"NaturalTransformation: OK"

  -- NaturalIsomorphism
  let iso : F ≅ₙ G := {
    toNatTrans := η
    inv := λ X => SetCat.id (F.mapObj X)
    leftInv := λ X => by simp
    rightInv := λ X => by simp
  }
  IO.println s!"NaturalIsomorphism: OK"

  -- Horizontal composition
  let hcomp := NaturalTransformation.hcomp η η
  IO.println s!"Horizontal composition: OK"

  -- Whiskering
  let wL := NaturalTransformation.whiskerLeft F η
  let wR := NaturalTransformation.whiskerRight η F
  IO.println s!"Whiskering left/right: OK"

  IO.println "Core coverage benchmark complete."
