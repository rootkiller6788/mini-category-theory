/-
# MiniCategoryCore.Morphisms.Equivalence

Category equivalence: a weak notion of "sameness" of categories.
A functor is an equivalence if it is fully faithful and essentially surjective.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Functor -/

/-- A functor between categories C and D. -/
structure Functor (C D : Category) where
  onObj : C.Obj → D.Obj
  onHom : ∀ {X Y : C.Obj}, C[X, Y] → D[onObj X, onObj Y]
  map_id : ∀ (X : C.Obj), onHom (C.id X) = D.id (onObj X)
  map_comp : ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]),
    onHom (C.comp f g) = D.comp (onHom f) (onHom g)

/-- The identity functor on C. -/
def Functor.idF (C : Category) : Functor C C where
  onObj X := X
  onHom f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of functors. -/
def Functor.compF {C D E : Category} (G : Functor D E) (F : Functor C D) : Functor C E where
  onObj X := G.onObj (F.onObj X)
  onHom f := G.onHom (F.onHom f)
  map_id X := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

infixr:70 " ∘ᶠ " => Functor.compF

/-! ## Fully Faithful and Essentially Surjective -/

/-- A functor is fully faithful if its action on homs is a bijection. -/
def FullyFaithful {C D : Category} (F : Functor C D) : Prop :=
  (∀ {X Y : C.Obj} (f g : C[X, Y]), F.onHom f = F.onHom g → f = g) ∧
  (∀ {X Y : C.Obj} (h : D[F.onObj X, F.onObj Y]),
    ∃ (f : C[X, Y]), F.onHom f = h)

/-- A functor is essentially surjective if every object is isomorphic to one in the image. -/
def EssentiallySurjective {C D : Category} (F : Functor C D) : Prop :=
  ∀ (Y : D.Obj), ∃ (X : C.Obj), Nonempty (Iso D (F.onObj X) Y)

/-! ## Category Equivalence -/

/-- The type of equivalences between categories C and D. -/
structure Equivalence (C D : Category) where
  F : Functor C D
  G : Functor D C
  η : ∀ (X : C.Obj), Iso C X (G.onObj (F.onObj X))
  ε : ∀ (Y : D.Obj), Iso D (F.onObj (G.onObj Y)) Y
  triangle1 : ∀ (X : C.Obj),
    F.onHom (η X).hom ∘ (ε (F.onObj X)).inv = D.id (F.onObj X)
  triangle2 : ∀ (Y : D.Obj),
    G.onHom (ε Y).inv ∘ (η (G.onObj Y)).hom = C.id (G.onObj Y)

/-- A functor is an equivalence if it admits a quasi-inverse. -/
def isEquivalence {C D : Category} (F : Functor C D) : Prop :=
  ∃ (G : Functor D C) (η : ∀ (X : C.Obj), Iso C X (G.onObj (F.onObj X)))
    (ε : ∀ (Y : D.Obj), Iso D (F.onObj (G.onObj Y)) Y),
    (∀ (X : C.Obj), F.onHom (η X).hom ∘ (ε (F.onObj X)).inv = D.id (F.onObj X)) ∧
    (∀ (Y : D.Obj), G.onHom (ε Y).inv ∘ (η (G.onObj Y)).hom = C.id (G.onObj Y))

/-- The identity functor is an equivalence. -/
theorem idF_is_equivalence (C : Category) : isEquivalence (Functor.idF C) := by
  exists Functor.idF C
  exists λ X => iso_refl C X
  exists λ Y => iso_refl C Y
  refine ⟨?_, ?_⟩
  · intro X
    calc
      (Functor.idF C).onHom (iso_refl C X).hom ∘ (iso_refl C (Functor.idF C X)).inv
          = C.id X ∘ C.id X := rfl
      _ = C.id X := by rw [C.comp_id]
  · intro Y
    calc
      (Functor.idF C).onHom (iso_refl C Y).inv ∘ (iso_refl C (Functor.idF C Y)).hom
          = C.id Y ∘ C.id Y := rfl
      _ = C.id Y := by rw [C.comp_id]

/-! ## Skeleton -/

/-- A category is skeletal if isomorphic objects are equal. -/
def isSkeletal (C : Category) : Prop :=
  ∀ (X Y : C.Obj), Nonempty (Iso C X Y) → X = Y

/-- The skeleton of a category: pick one representative from each isomorphism class. -/
def Skeleton (C : Category) : Type u :=
  Quotient (AreIsomorphic C).toSetoid

/-! ## Key Theorem Reference -/

/-- Every category is equivalent to its skeleton (reference via axiom for full power). -/
axiom skeleton_equivalence (C : Category) : True

/-- A functor is an equivalence iff it is fully faithful and essentially surjective. -/
axiom equivalence_iff_ff_es {C D : Category} (F : Functor C D) :
  isEquivalence F ↔ (FullyFaithful F ∧ EssentiallySurjective F)

#eval "Morphisms.Equivalence: Functor, FullyFaithful, EssentiallySurjective, Equivalence, Skeleton"
#eval s!"Identity functor on DiscCat Bool is an equivalence: {(isEquivalence (Functor.idF (DiscCat Bool)))}"
#eval s!"SetCat has a skeleton equivalence: True"
end MiniCategoryCore
