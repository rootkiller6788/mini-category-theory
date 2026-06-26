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

/-! ## Whisker-Whisker Exchange -/

/--
Left and right whiskering commute: given α : F ⇒ G (B → C), β : G ⇒ H (C → D),
and K : D → E, we have K ∘ (β ∘ α) = (K ∘ β) ∘ α.
-/
theorem whiskerLeft_whiskerRight_exchange {B C D E : Category}
    (F : Functor B C) {G H : Functor C D} (α : G ⇒ H) (K : Functor D E) :
    NaturalTransformation.whiskerRight (NaturalTransformation.whiskerLeft F α) K =
    NaturalTransformation.whiskerLeft F (NaturalTransformation.whiskerRight α K) := by
  funext X; rfl

/--
Triple whiskering: left and right whiskering operations are compatible
under composition with multiple functors.
-/
theorem whiskering_compatibility {A B C D E : Category}
    (A_f : Functor A B) {F G : Functor B C} (α : F ⇒ G)
    (D_f : Functor C D) (E_f : Functor D E) :
    NaturalTransformation.whiskerRight
      (NaturalTransformation.whiskerLeft A_f (NaturalTransformation.whiskerRight α D_f)) E_f =
    NaturalTransformation.whiskerRight
      (NaturalTransformation.whiskerRight (NaturalTransformation.whiskerLeft A_f α) D_f) E_f := by
  funext X; rfl

/-! ## Double Naturality -/

/--
Given natural transformations α : F ⇒ G and β : H ⇒ K, and a morphism
f : X → Y, the double naturality square commutes.
-/
theorem double_naturality {C D : Category}
    {F G H K : Functor C D} (α : F ⇒ G) (β : H ⇒ K)
    {X Y : C.Obj} (f : C[X, Y]) :
    D.comp (D.comp (β.component Y) (α.component Y)) (F.mapHom f) =
    D.comp (D.comp (K.mapHom f) (β.component X)) (α.component X) := by
  calc
    D.comp (D.comp (β.component Y) (α.component Y)) (F.mapHom f) =
      D.comp (β.component Y) (D.comp (α.component Y) (F.mapHom f)) := by
      simp [D.assoc]
    _ = D.comp (β.component Y) (D.comp (G.mapHom f) (α.component X)) := by
      rw [α.naturality]
    _ = D.comp (D.comp (β.component Y) (G.mapHom f)) (α.component X) := by
      simp [D.assoc]
    _ = D.comp (D.comp (K.mapHom f) (β.component X)) (α.component X) := by
      rw [β.naturality]

/-! ## #eval Examples -/

#eval "Core.Laws: naturalitySquare, vcomp_assoc, interchangeLaw, whiskerLeft_vcomp, whiskerRight_vcomp"
#eval "whiskerLeft_whiskerRight_exchange, whiskering_compatibility, double_naturality"
#eval s!"Vertical associativity: (γ ∘ β) ∘ α = γ ∘ (β ∘ α)"
#eval s!"Interchange law (middle-four exchange) verified"
#eval s!"Double naturality: β_Y ∘ α_Y ∘ Ff = Kf ∘ β_X ∘ α_X"
