import MiniCategoryCore

open MiniCategoryCore

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniCategoryCore v0.1.0"
  IO.println "  Category Theory Core: Category, SetCat, Opposite, Product"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Category: Obj, Hom, id, comp with identity and associativity laws"
  IO.println s!"  SetCat: the category of types and functions"
  IO.println s!"  Cᵒᵖ: opposite category with reversed morphisms"
  IO.println s!"  C ×ᶜ D: product category of pairs of objects and morphisms"
  IO.println s!"  DiscCat A: discrete category (only identity morphisms)"
  IO.println s!"  CodiscCat A: codiscrete category (exactly one morphism per pair)"
  IO.println s!"  Notation: C[X, Y] for hom-sets, f ∘ g for composition"
  IO.println ""
  IO.println "  Depends on: mini-object-kernel"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
