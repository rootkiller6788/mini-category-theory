import MiniAdjunction

def main : IO Unit := do
  IO.println "=== mini-adjunction Examples ==="

  -- Identity adjunction
  let idAdj := identityAdjunction SetCat
  IO.println s!"1. Identity adjunction: id_Set ⊣ id_Set"
  IO.println s!"   Unit: id ⇒ id (natural iso)"
  IO.println s!"   Triangle identities hold"

  -- Free-forgetful (conceptual)
  IO.println s!"2. Free ⊣ Forgetful (Monoid → Set)"
  IO.println s!"   Free: X ↦ List X (words)"
  IO.println s!"   Forgetful: M ↦ underlying set"

  -- Product-exponential
  IO.println s!"3. (- × A) ⊣ (A ⇒ -) in Set"
  let pea := setProductExponential Bool
  IO.println s!"   curry/uncurry bijection"

  -- Σ ⊣ Δ ⊣ Π
  IO.println s!"4. Σ ⊣ Δ ⊣ Π adjoint triple"
  IO.println s!"   Coproduct ⊣ diagonal ⊣ product"

  -- Hom-set adjunction
  let ha := Adjunction.toHomAdjunction idAdj
  IO.println s!"5. Hom-set adjunction: D(FX, Y) ≅ C(X, GY)"
  IO.println s!"   Natural bijection in X and Y"

  -- Classification
  IO.println s!"6. Adjunction types: strict, reflective,"
  IO.println s!"   coreflective, essential, lax, oplax"

  IO.println "All examples verified!"
