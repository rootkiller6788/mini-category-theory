import MiniFunctorCore

open MiniFunctorCore
open MiniCategoryCore
open MiniMorphismSystem

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniFunctorCore v0.1.0"
  IO.println "  Functor Categories, Diagrams, Hom-Functors, Presheaves"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  FunctorCategory [C, D]: functors as objects, natural transformations as morphisms"
  IO.println s!"  homFunctor C X: covariant hom-functor C(X, -) : C → Set"
  IO.println s!"  homFunctorOp C X: contravariant hom-functor C(-, X) : Cᵒᵖ → Set"
  IO.println s!"  diag: diagonal functor Δ : D → [C, D]"
  IO.println s!"  eval X: evaluation functor ev_X : [C, D] → D"
  IO.println s!"  SliceCat / CosliceCat: slice and coslice over/under an object"
  IO.println s!"  ArrowCat: arrow category C^→"
  IO.println s!"  PresheafCategory: functor category [Cᵒᵖ, Set]"
  IO.println s!"  TwistedArrowCat: twisted arrow category Tw(C)"
  IO.println ""
  IO.println "  Depends on: mini-category-core, mini-morphism-system"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
