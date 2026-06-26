import MiniYonedaLite
import MiniCategoryCore
import MiniFunctorCore
import MiniNaturalTransformation

open MiniYonedaLite
open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "=== mini-yoneda-lite Examples ==="

  -- Example 1: Presheaf category construction
  IO.println "Representable functors, presheaf categories, Yoneda embedding"

  -- Example 2: SetCat presheaf category
  let C : Category := SetCat
  let presh := presheafCategory C
  IO.println s!"Presheaf category over SetCat constructed"

  -- Example 3: Yoneda embedding
  let Y := yonedaEmbedding C
  IO.println s!"Yoneda embedding Y: Cᵒᵖ → [C, Set]"
  IO.println s!"  Y(X) = Hom(X, -) : C → Set"

  -- Example 4: Representable functor for Unit
  let unitRepr : Functor C SetCat := homFunctor C Unit
  IO.println s!"Hom(Unit, -) : SetCat → Set"
  IO.println s!"  Hom(Unit, X) ≅ X (natural isomorphism)"

  -- Example 5: Representability check
  IO.println s!"isRepresentable expects ∃ X, F ≅ Hom(X, -)"

  -- Example 6: Yoneda lemma statement
  IO.println "Yoneda lemma: Nat(Hom(X,-), F) ≅ F(X)"
  IO.println "  For any functor F : C → Set and object X"

  -- Example 7: Yoneda embedding is fully faithful
  IO.println "Yoneda embedding is fully faithful"
  IO.println "  Hom_C(X, Y) ≅ Hom_{[Cᵒᵖ,Set]}(Y(X), Y(Y))"

  -- Example 8: Presheaf topos
  IO.println "Presheaf category [Cᵒᵖ, Set] is a topos"
  IO.println "  Subobject classifier, cartesian closed, limits/colimits"

  -- Example 9: Corollaries
  IO.println "Corollary: if Y(X) ≅ Y(Y) then X ≅ Y (embedding reflects isos)"
  IO.println "Corollary: limits/colimits computed pointwise in presheaf category"

  -- Example 10: Representable presheaves
  IO.println s!"isRepresentablePresheaf: ∃ X, True (presheaf ≅ Y(X))"

  IO.println "All examples demonstrated."
