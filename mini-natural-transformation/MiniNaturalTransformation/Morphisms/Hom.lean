/-
# MiniNaturalTransformation.Morphisms.Hom

Horizontal composition and the 2-categorical structure of Cat.
Natural transformations as 2-morphisms, with modifications between them.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Hom
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Core.Laws

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Horizontal Composition via Whiskering -/

/--
Horizontal composition of natural transformations via the whiskering
decomposition: β ∘ₕ α = (β * G) ∘ᵥ (H * α) for α : F ⇒ G, β : H ⇒ K.
-/
def NaturalTransformation.hcomp {C D E : Category}
    {F G : Functor C D} {H K : Functor D E}
    (β : H ⇒ K) (α : F ⇒ G) :
    Functor.comp F H ⇒ Functor.comp G K :=
  NaturalTransformation.vcomp
    (NaturalTransformation.whiskerRight β G)
    (NaturalTransformation.whiskerLeft F α)

infixr:60 " ∘ₕ " => NaturalTransformation.hcomp

/-! ## 2-Category Structure of Cat -/

/--
Cat is a strict 2-category: objects are categories, 1-morphisms are
functors, and 2-morphisms are natural transformations.

The horizontal composition satisfies:
- Left unit: id_H ∘ₕ α = α
- Right unit: β ∘ₕ id_F = β
- Interchange: (δ ∘ᵥ γ) ∘ₕ (β ∘ᵥ α) = (δ ∘ₕ β) ∘ᵥ (γ ∘ₕ α)
-/

/--
Horizontal composition with identity on the left is whiskering on the left:
id_H ∘ₕ α = H*α.
-/
theorem hcomp_id_left {C D E : Category}
    {F G : Functor C D} (H : Functor D E) (α : F ⇒ G) :
    NaturalTransformation.hcomp (NaturalTransformation.id H) α =
    NaturalTransformation.whiskerLeft H α := by
  funext X; simp [NaturalTransformation.hcomp, NaturalTransformation.whiskerLeft,
    NaturalTransformation.whiskerRight, NaturalTransformation.vcomp, NaturalTransformation.id]

/--
Horizontal composition with identity on the right is whiskering on the right:
β ∘ₕ id_F = β*F.
-/
theorem hcomp_id_right {C D E : Category}
    {H K : Functor D E} (β : H ⇒ K) (F : Functor C D) :
    NaturalTransformation.hcomp β (NaturalTransformation.id F) =
    NaturalTransformation.whiskerRight β F := by
  funext X; simp [NaturalTransformation.hcomp, NaturalTransformation.whiskerLeft,
    NaturalTransformation.whiskerRight, NaturalTransformation.vcomp, NaturalTransformation.id]

/-! ## Modification between Natural Transformations -/

/--
A modification m : α ⇛ β between natural transformations α, β : F ⇒ G
is a family of 2-cells m_X : α_X → β_X satisfying a coherence condition
that makes the following cylinder diagram commute:
For each f : X → Y in C, we have:
  β_Y ∘ F(f) = G(f) ∘ β_X  (naturality of β)
  α_Y ∘ F(f) = G(f) ∘ α_X  (naturality of α)
  m_Y ∘ α_Y = β_Y ∘ m_X   (modification condition)

In Cat, a modification is a natural transformation between natural
transformations, making Cat a 3-dimensional categorical structure.
-/
structure Modification {C D : Category} {F G : Functor C D}
    (α β : F ⇒ G) where
  component : ∀ (X : C.Obj), D[F.mapObj X, F.mapObj X]
  modificationNatural : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (α.component Y) = D.comp (β.component Y) (component X)

/--
The identity modification on a natural transformation α has
component-wise identity 2-cells.
-/
def Modification.id {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) : Modification α α where
  component X := D.id (F.mapObj X)
  modificationNatural {X Y} f := by
    simp

/--
Vertical composition of modifications: given m : α ⇛ β and n : β ⇛ γ,
produce n ∘ m : α ⇛ γ with component (n_X ∘ m_X).
-/
def Modification.vcomp {C D : Category} {F G : Functor C D}
    {α β γ : F ⇒ G} (n : Modification β γ) (m : Modification α β) :
    Modification α γ where
  component X := D.comp (n.component X) (m.component X)
  modificationNatural {X Y} f := by
    calc
      D.comp (D.comp (n.component Y) (m.component Y)) (α.component Y) =
        D.comp (n.component Y) (D.comp (m.component Y) (α.component Y)) := by
        simp [D.assoc]
      _ = D.comp (n.component Y) (D.comp (β.component Y) (m.component X)) := by
        rw [m.modificationNatural]
      _ = D.comp (D.comp (n.component Y) (β.component Y)) (m.component X) := by
        simp [D.assoc]
      _ = D.comp (D.comp (γ.component Y) (n.component X)) (m.component X) := by
        rw [n.modificationNatural]
      _ = D.comp (γ.component Y) (D.comp (n.component X) (m.component X)) := by
        simp [D.assoc]

/-! ## #eval Examples -/

/-- Horizontal composition of identity on maybeFunctor with identity on listFunctor. -/
def hcompExample : Functor.comp listFunctor maybeFunctor ⇒
    Functor.comp listFunctor maybeFunctor :=
  NaturalTransformation.hcomp (NaturalTransformation.id maybeFunctor)
    (NaturalTransformation.id listFunctor)

/-- The identity modification on id_{listFunctor}. -/
def idModExample : Modification (NaturalTransformation.id listFunctor)
    (NaturalTransformation.id listFunctor) :=
  Modification.id (NaturalTransformation.id listFunctor)

#eval "Morphisms.Hom: hcomp (∘ₕ), hcomp_id_left, hcomp_id_right, Modification, Modification.id, Modification.vcomp"
#eval s!"Horizontal composition: β ∘ₕ α = (β*G) ∘ᵥ (H*α)"
#eval s!"Cat is a strict 2-category"
#eval s!"Modifications: 3-dimensional structure on Cat"
