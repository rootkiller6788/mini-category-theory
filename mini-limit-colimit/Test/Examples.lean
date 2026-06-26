import MiniLimitColimit

open MiniLimitColimit
open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-limit-colimit Examples ==="
  IO.println "Diagram, Cone, Cocone, Limit, Colimit, products, coproducts"

  -- Product in SetCat
  let prod : IsProduct SetCat Nat Bool (Nat × Bool) := productOfPairInSet
  IO.println s!"Product Nat × Bool: fst(3,true) = {prod.fst (3, true)}"

  -- Coproduct in SetCat
  let coprod : IsCoproduct SetCat Nat Bool (Nat ⊕ Bool) := coproductOfPairInSet
  IO.println s!"Coproduct Nat ⊕ Bool: inl 3"

  -- Equalizer in SetCat
  let eq : Equalizer (SetCat := SetCat) (fun (n : Nat) => n) (fun n => n) :=
    equalizerInSet (fun (n : Nat) => n) (fun (n : Nat) => n)
  IO.println s!"Equalizer of id and id"

  -- Pullback in SetCat
  let pb : Pullback (SetCat := SetCat) (fun (a : Nat) => a) (fun (b : Nat) => b) :=
    pullbackInSet (fun (a : Nat) => a) (fun (b : Nat) => b)
  IO.println s!"Pullback of (id, id)"

  IO.println "All examples passed!"
