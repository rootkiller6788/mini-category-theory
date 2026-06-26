/-
# MiniNaturalTransformation.Constructions.Universal

Universal natural transformations and universal arrows. A universal
arrow from X to F is an initial object in the comma category (X ↓ F).
Here we characterize universal natural transformations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Universal Natural Transformation -/

/--
A natural transformation η : Δ_A ⇒ F (from the constant functor at A
to a functor F : C → D) is universal if for any other β : Δ_B ⇒ F,
there exists a unique f : B → A such that β = η ∘ Δ_f.

This characterizes a universal arrow A → F as an initial object
in the comma category (Δ ↓ F).
-/
structure UniversalNatTrans {C D : Category} (A : D.Obj) (F : Functor C D) where
  constA : Functor C D := Functor.const C D A
  eta : constA ⇒ F
  universal : ∀ (B : D.Obj) (β : Functor.const C D B ⇒ F),
    ∃! (f : D[B, A]),
      NaturalTransformation.vcomp eta
        { component := λ _ => f
          naturality := λ _ => by simp } = β

/-! ## Universal Property via Natural Transformations -/

/--
A universal natural transformation property: for each object X of C,
the component η_X : A → F(X) is a universal arrow in D.
-/
def isUniversalComponent {C D : Category} (A : D.Obj)
    (F : Functor C D) (η : Functor.const C D A ⇒ F) : Prop :=
  ∀ (X : C.Obj), ∀ (B : D.Obj) (g : D[B, F.mapObj X]),
    ∃! (f : D[B, A]), D.comp (η.component X) f = g

/-! ## Universal Arrow as Natural Transformation -/

/--
A universal arrow from A to F is encoded as a natural transformation
η : Δ_A ⇒ F that is componentwise universal.
-/
structure UniversalArrow {C D : Category} (A : D.Obj) (F : Functor C D) where
  arrow : Functor.const C D A ⇒ F
  componentUniversal : ∀ (X : C.Obj), ∀ (B : D.Obj) (g : D[B, F.mapObj X]),
    ∃! (f : D[B, A]), D.comp (arrow.component X) f = g

/-! ## Identity Natural Transformation is Universal -/

/--
The identity natural transformation id : Δ_A ⇒ Δ_A is trivially universal.
-/
def idUniversal {C D : Category} (A : D.Obj) :
    UniversalArrow A (Functor.const C D A) where
  arrow := NaturalTransformation.id (Functor.const C D A)
  componentUniversal X B g := by
    refine ⟨g, ?_, λ f h => ?_⟩
    · simp [NaturalTransformation.id]
    · simpa [NaturalTransformation.id] using h

/-! ## #eval Examples -/

/-- The identity natural transformation Δ_Nat ⇒ Δ_Nat is universal. -/
def constNatUniversal : UniversalArrow Nat constNat := idUniversal Nat

#eval "Constructions.Universal: UniversalNatTrans, isUniversalComponent, UniversalArrow, idUniversal"
#eval s!"Universal arrow from Nat to constNat (trivial)"
#eval s!"Universal property characterizes adjunctions"
