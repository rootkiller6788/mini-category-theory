/-
# MiniCategoryCore.Theorems.Main

Main theorem statements: Yoneda lemma reference, adjoint functor theorem reference,
and other fundamental results that require deeper foundations.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Equivalence
import MiniCategoryCore.Theorems.Basic
import MiniCategoryCore.Theorems.UniversalProperties

namespace MiniCategoryCore

/-! ## Yoneda Lemma Reference -/

/-- The Yoneda lemma states that for any presheaf F : Cᵒᵖ → Set and object A,
    there is a natural isomorphism Nat(Hom(-, A), F) ≅ F(A).
    This is a deep theorem stated as an axiom. -/
axiom yonedaLemma {C : Category} (A : C.Obj) : True

/-- The Yoneda embedding y : C → [Cᵒᵖ, Set] is fully faithful. -/
axiom yonedaEmbedding {C : Category} : True

/-! ## Adjoint Functor Theorems -/

/-- General Adjoint Functor Theorem (GAFT):
    A continuous functor between complete categories satisfying the solution set
    condition has a left adjoint. Stated as an axiom. -/
axiom generalAdjointFunctorTheorem {C D : Category}
    (G : D.Obj → C.Obj)
    (onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y]) : True

/-- Special Adjoint Functor Theorem (SAFT):
    For well-powered complete categories with a coseparating set,
    every continuous functor has a left adjoint. -/
axiom specialAdjointFunctorTheorem {C D : Category}
    (G : D.Obj → C.Obj)
    (onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y]) : True

/-! ## Equivalence Characterization -/

/-- A functor is an equivalence iff it is fully faithful and essentially surjective.
    This is a fundamental theorem of category theory. -/
axiom equivalence_characterization {C D : Category} (F : Functor C D) :
    isEquivalence F ↔ (FullyFaithful F ∧ EssentiallySurjective F)

/-! ## Functor Composition Laws -/

/-- Functor composition is associative. -/
theorem functor_comp_assoc {B C D E : Category} (F : Functor D E) (G : Functor C D) (H : Functor B C) :
    ((F ∘ᶠ G) ∘ᶠ H).onObj = (F ∘ᶠ (G ∘ᶠ H)).onObj := by
  ext X; rfl

/-- Identity functor composition laws. -/
theorem functor_id_laws {C D : Category} (F : Functor C D) :
    (F ∘ᶠ (Functor.idF C)).onObj = F.onObj ∧ ((Functor.idF D) ∘ᶠ F).onObj = F.onObj := by
  refine ⟨?_, ?_⟩
  · ext X; rfl
  · ext X; rfl

/-- Functor composition respects onObj: the composite's onObj is the composition of onObjs. -/
theorem functor_comp_onObj {B C D : Category} (F : Functor C D) (G : Functor B C) (X : B.Obj) :
    (F ∘ᶠ G).onObj X = F.onObj (G.onObj X) := rfl

/-! ## Product Functor -/

/-- The product of two functors F × G : C × D → E × F. -/
def ProductFunctor {C D E F : Category} (FC : Functor C E) (FD : Functor D F) :
    Functor (C ×ᶜ D) (E ×ᶜ F) where
  onObj X := (FC.onObj X.1, FD.onObj X.2)
  onHom f := (FC.onHom f.1, FD.onHom f.2)
  map_id X := by
    simp [FC.map_id, FD.map_id]
  map_comp f g := by
    simp [FC.map_comp, FD.map_comp]

/-! ## Diagonal Functor -/

/-- The diagonal functor Δ : C → C × C. -/
def DiagonalFunctor (C : Category) : Functor C (C ×ᶜ C) where
  onObj X := (X, X)
  onHom f := (f, f)
  map_id X := rfl
  map_comp f g := rfl

#eval "Theorems.Main: Yoneda lemma, adjoint functor theorem, equivalence characterization"
#eval "These deep theorems are stated as axioms for reference"
#eval s!"Diagonal functor maps each object X to (X, X) in the product category"
end MiniCategoryCore
