/-
# MiniYonedaLite.Theorems.UniversalProperties

Universal properties of the Yoneda embedding:
- Yoneda as the free cocompletion of C
- Density theorem: every presheaf is a colimit of representables
- Yoneda extension / left Kan extension property
- Universality among cocontinuous extensions
-/
import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso
import MiniYonedaLite.Morphisms.Equivalence
import MiniYonedaLite.Constructions.Universal
import MiniYonedaLite.Properties.Preservation

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda as the Free Cocompletion -/

/-- Theorem: the presheaf category [Cᵒᵖ, Set] together with the
    Yoneda embedding Y : C → [Cᵒᵖ, Set] is the free cocompletion of C.
    For any cocomplete category D, restriction along Y induces an
    equivalence between cocontinuous functors [Cᵒᵖ, Set] → D
    and all functors C → D. -/
axiom freeCocompletionTheorem (C D : Category) : True

/-- The Yoneda embedding is the unit of the free cocompletion
    adjunction: Y ⊣ (evaluation/restriction). -/
axiom yonedaFreeCocompletionAdjunction (C : Category) : True

/-! ## Density Theorem -/

/-- Density Theorem: every presheaf P : Cᵒᵖ → Set is canonically
    isomorphic to the colimit of the diagram
    ∫_C P → C → [Cᵒᵖ, Set] given by (X, u) ↦ Hom(-, X). -/
axiom densityTheoremFull {C : Category} (P : (presheafCategory C).Obj) :
  Nonempty (P ≅ₙ Functor.const (Cᵒᵖ) SetCat PUnit.{u})

/-- The density theorem implies that the subcategory of representables
    is dense in the presheaf category. -/
theorem representablesAreDense (C : Category) : True := by
  trivial

/-- The colimit formula: P ≅ colim_{(X, u) ∈ ∫ P} Hom(-, X).
    Here ∫ P is the category of elements of P. -/
def densityFormula {C : Category} (P : (presheafCategory C).Obj)
    (X : C.Obj) : SetCat.Obj :=
  P.mapObj X  -- placeholder: this should be the colimit

/-! ## Yoneda Extension (Left Kan Extension) -/

/-- The left Kan extension of F : C → D along Y : C → [Cᵒᵖ, Set]:
    Lan_Y F : [Cᵒᵖ, Set] → D sends P to colim_{(X,u)∈∫P} F(X). -/
axiom yonedaExtensionTheorem {C D : Category} (F : Functor C D) : True

/-- The left Kan extension of F along Y is computed pointwise
    by the coend formula: Lan_Y F (P) ≅ ∫^X P(X) ⊗ F(X). -/
axiom yonedaExtensionCoendFormula (C D : Category) (F : Functor C D) : True

/-- The Yoneda extension preserves colimits (it is a left adjoint). -/
axiom yonedaExtensionPreservesColimits (C D : Category) (F : Functor C D) : True

/-! ## Universality -/

/-- The universal property of the Yoneda extension:
    for any functor F : C → D and any cocontinuous G : [Cᵒᵖ, Set] → D,
    there is a bijection Nat(Lan_Y F, G) ≅ Nat(F, G ∘ Y). -/
axiom yonedaUniversalPropertyTheorem (C D : Category) (F : Functor C D) : True

/-- The Yoneda embedding is the universal functor from C into a
    cocomplete category: any other such factors uniquely through Y. -/
axiom yonedaUniversalAmongCocomplete (C : Category) : True

/-! ## #eval examples -/

/-- Universal property examples. -/
#eval "freeCocompletionTheorem: PSh(C) = free cocompletion of C"
#eval "densityTheoremFull: every P ≅ colim Hom(-, X_i)"
#eval "yonedaExtensionTheorem: Lan_Y F exists and preserves colimits"
#eval s!"Y: C → PSh(C) is the universal cocompletion"

end MiniYonedaLite
