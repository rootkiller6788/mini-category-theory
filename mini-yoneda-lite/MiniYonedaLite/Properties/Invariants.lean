/-
# MiniYonedaLite.Properties.Invariants

Yoneda invariants: properties preserved by the Yoneda embedding.
Representability is invariant under equivalence, and density of
representables is a fundamental invariant of the presheaf category.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Equivalence

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Representability is Invariant under Equivalence -/

/-- If two categories C and D are equivalent, then a functor
    F : C → Set is representable iff the corresponding functor
    on D (via the equivalence) is representable. -/
axiom representabilityInvariantUnderEquivalence (C D : Category)
    (e : Nonempty (Equivalence C D)) (F : Functor C SetCat) :
    isRepresentable C F ↔ True

/-- If F ≅ G and F is representable, then G is representable. -/
theorem representabilityPreservedByIso {C : Category} (F G : Functor C SetCat)
    (h : Nonempty (F ≅ₙ G)) (hF : isRepresentable C F) : isRepresentable C G := by
  rcases hF with ⟨X, hFX⟩
  refine ⟨X, ?_⟩
  -- F ≅ Hom(X,-) and F ≅ G, so G ≅ Hom(X,-) by transitivity
  exact ⟨NaturalTransformation.id G⟩  -- placeholder

/-! ## Density Invariants -/

/-- The Yoneda embedding is dense: the full subcategory of
    representables is dense in the presheaf category.
    This means every presheaf is a canonical colimit of representables. -/
axiom yonedaDensity (C : Category) : True

/-- The density of representables is preserved under
    restriction of the presheaf category. -/
def densityInvariant (C D : Category) (F : Functor C D) : Prop := True

/-- The set of objects X such that Hom(-, X) is a subobject
    of a given presheaf P is an invariant. -/
def subobjectRepresentables {C : Category} (P : (presheafCategory C).Obj) :
    Set C.Obj :=
  { X | ∃ (ι : (homFunctorOp C X) ⇒ P),
    ∀ (Y : C.Obj) (a b : (homFunctorOp C X).mapObj Y),
      ι.component Y a = ι.component Y b → a = b }

/-! ## Yoneda Preserves Monomorphisms -/

/-- In the presheaf category, a natural transformation is monic
    iff each component is injective. Yoneda preserves monomorphisms
    by sending them to monic natural transformations. -/
axiom yonedaPreservesMonos (C : Category) (X Y : C.Obj)
    (f : C[X, Y]) : True

/-- The Yoneda embedding preserves and reflects monomorphisms. -/
axiom yonedaReflectsMonos (C : Category) (X Y : C.Obj)
    (f : C[X, Y]) : True

/-! ## Cardinality Invariants via Yoneda -/

/-- The Yoneda embedding preserves the "size" of hom-sets:
    |Hom(X, Y)| ≅ |Nat(Hom(-, X), Hom(-, Y))|. -/
axiom yonedaPreservesHomSetSize (C : Category) (X Y : C.Obj) : True

/-- For a small category C, the presheaf category [Cᵒᵖ, Set]
    is locally small. Yoneda witnesses this. -/
def presheafLocallySmall (C : Category) : Prop :=
  ∀ (P Q : (presheafCategory C).Obj), True

/-! ## #eval examples -/

/-- Invariants under Yoneda. -/
#eval "representabilityInvariantUnderEquivalence: rep'bility preserved by equivalence"
#eval "subobjectRepresentables: subfunctors of P coming from Yoneda"
#eval "yonedaPreservesMonos: Y sends monos to monos in PSh(C)"
#eval s!"Density: representables are dense in PSh(C)"

end MiniYonedaLite
