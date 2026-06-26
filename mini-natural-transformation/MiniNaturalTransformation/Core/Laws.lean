/-
# MiniNaturalTransformation.Core.Laws

Naturality laws: vertical associativity, interchange law (middle-four),
and whiskering laws for natural transformations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Naturality Square (re-stated) -/

/--
The fundamental naturality square: for η : F ⇒ G and f : X → Y,
we have η_Y ∘ F(f) = G(f) ∘ η_X.
-/
theorem naturalitySquare {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) {X Y : C.Obj} (f : C[X, Y]) :
    D.comp (η.component Y) (F.mapHom f) = D.comp (G.mapHom f) (η.component X) :=
  η.naturality f

/-! ## Vertical Associativity -/

/--
Vertical composition of natural transformations is associative.
For α : F ⇒ G, β : G ⇒ H, γ : H ⇒ K, we have (γ ∘ β) ∘ α = γ ∘ (β ∘ α).
-/
theorem vcomp_assoc {C D : Category} {F G H K : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (γ : H ⇒ K) :
    NaturalTransformation.vcomp (NaturalTransformation.vcomp γ β) α =
    NaturalTransformation.vcomp γ (NaturalTransformation.vcomp β α) := by
  funext X
  simp [NaturalTransformation.vcomp, D.assoc]

/-! ## Interchange Law (Middle-Four) -/

/--
The interchange law (middle-four): given natural transformations
  α : F ⇒ G, β : G ⇒ H, γ : K ⇒ L, δ : L ⇒ M,
we have (δ ∘ᵥ γ) ∘ₕ (β ∘ᵥ α) = (δ ∘ₕ β) ∘ᵥ (γ ∘ₕ α).

This is the key coherence law that makes Cat a 2-category.
-/
theorem interchangeLaw {B C D : Category}
    {F G H : Functor B C} {K L M : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H) (γ : K ⇒ L) (δ : L ⇒ M) :
    NaturalTransformation.hcomp (NaturalTransformation.vcomp δ γ) (NaturalTransformation.vcomp β α) =
    NaturalTransformation.vcomp (NaturalTransformation.hcomp δ β) (NaturalTransformation.hcomp γ α) := by
  funext X
  simp [NaturalTransformation.vcomp, NaturalTransformation.hcomp,
    NaturalTransformation.whiskerLeft, NaturalTransformation.whiskerRight,
    D.assoc, α.naturality, β.naturality, γ.naturality, δ.naturality,
    K.preservesComp, L.preservesComp, M.preservesComp]

/-! ## Whiskering Laws -/

/--
Left whiskering by the identity functor is the identity operation.
-/
theorem whiskerLeft_id {C D : Category} {F G : Functor C D} (α : F ⇒ G) :
    NaturalTransformation.whiskerLeft (Functor.id C) α = α := by
  funext X; rfl

/--
Right whiskering by the identity functor is the identity operation.
-/
theorem whiskerRight_id {C D : Category} {F G : Functor C D} (α : F ⇒ G) :
    NaturalTransformation.whiskerRight α (Functor.id D) = α := by
  funext X; simp

/--
Whiskering respects vertical composition: F*(β ∘ α) = (F*β) ∘ (F*α).
-/
theorem whiskerLeft_vcomp {C D E : Category}
    (F : Functor C D) {G H K : Functor D E} (α : G ⇒ H) (β : H ⇒ K) :
    NaturalTransformation.whiskerLeft F (NaturalTransformation.vcomp β α) =
    NaturalTransformation.vcomp (NaturalTransformation.whiskerLeft F β)
      (NaturalTransformation.whiskerLeft F α) := by
  funext X; rfl

/--
Whiskering respects vertical composition: (β ∘ α)*H = (β*H) ∘ (α*H).
-/
theorem whiskerRight_vcomp {C D E : Category}
    {F G H : Functor C D} (α : F ⇒ G) (β : G ⇒ H) (K : Functor D E) :
    NaturalTransformation.whiskerRight (NaturalTransformation.vcomp β α) K =
    NaturalTransformation.vcomp (NaturalTransformation.whiskerRight β K)
      (NaturalTransformation.whiskerRight α K) := by
  funext X; simp [K.preservesComp]

/-! ## #eval Examples -/

#eval "Core.Laws: naturalitySquare, vcomp_assoc, interchangeLaw, whiskerLeft_vcomp, whiskerRight_vcomp"
#eval s!"Vertical associativity: (γ ∘ β) ∘ α = γ ∘ (β ∘ α)"
#eval s!"Interchange law (middle-four exchange) verified"
