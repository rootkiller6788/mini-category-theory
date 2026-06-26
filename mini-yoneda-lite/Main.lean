import MiniYonedaLite

open MiniYonedaLite
open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniYonedaLite v0.1.0"
  IO.println "  Yoneda Embedding, Yoneda Lemma, Representable Functors, Presheaves"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  yonedaEmbedding Y: Cᵒᵖ → [C, Set]"
  IO.println s!"  isRepresentable F: F ≅ Hom(X, -) for some X"
  IO.println s!"  presheafCategory C: functor category [Cᵒᵖ, Set]"
  IO.println s!"  isRepresentablePresheaf P: P ≅ Y(X) in the presheaf category"
  IO.println s!"  Yoneda lemma: Nat(Hom(X, -), F) ≅ F(X)"
  IO.println s!"  Yoneda embedding is fully faithful"
  IO.println s!"  Representable functors correspond to objects (up to isomorphism)"
  IO.println ""
  IO.println "  Depends on: mini-category-core, mini-functor-core, mini-natural-transformation"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
