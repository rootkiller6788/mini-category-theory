/-
Main entry point for mini-limit-colimit.
Prints package info and basic diagnostics.
-/

import MiniLimitColimit

open MiniLimitColimit
open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-limit-colimit ==="
  IO.println "Limits and colimits: Diagram, Cone, Cocone, Limit, Colimit"
  IO.println "Products, coproducts, equalizers, coequalizers, pullbacks, pushouts"
  IO.println "Depends on: mini-category-core, mini-functor-core, mini-natural-transformation"

  -- Verify key definitions are accessible
  let C : Category := SetCat

  -- Product
  let prod : IsProduct SetCat Nat Bool (Nat × Bool) := productOfPairInSet
  IO.println s!"Product: Nat × Bool | fst(3,true) = {prod.fst (3,true)} | snd(3,true) = {prod.snd (3,true)}"

  -- Coproduct
  let coprod : IsCoproduct SetCat Nat Bool (Nat ⊕ Bool) := coproductOfPairInSet
  IO.println s!"Coproduct: Nat ⊕ Bool | inl 5 = {coprod.inl 5}"

  -- Cone construction
  let D : Diagram (DiscCat (Fin 2)) SetCat := productDiagram SetCat Nat Bool
  let c : Cone D := {
    apex := Nat × Bool
    proj
      | 0 => Prod.fst
      | 1 => Prod.snd
    naturality _ := by simp
  }
  IO.println s!"Cone apex: {c.apex}"

  -- Complete checking
  let complete : Prop := IsComplete SetCat
  IO.println s!"IsComplete SetCat: {complete}"

  IO.println "mini-limit-colimit loaded successfully!"
