import MiniAdjunction

open MiniAdjunction
open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniAdjunction v0.1.0"
  IO.println "  Adjunctions: F ⊣ G via Unit/Counit and Hom-Set Adjunction"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Adjunction F G: unit and counit with triangle identities"
  IO.println s!"  Notation: F ⊣ G"
  IO.println s!"  FreeForgetful: free ⊣ forgetful adjunction pattern"
  IO.println s!"  Hom-set adjunction: Hom(FX, Y) ≅ Hom(X, GY) natural in X, Y"
  IO.println s!"  Triangle identities: (Gε) ∘ (ηG) = id_G, (εF) ∘ (Fη) = id_F"
  IO.println s!"  Adjoints are unique up to natural isomorphism"
  IO.println ""
  IO.println "  Depends on: mini-category-core, mini-functor-core, mini-natural-transformation"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
