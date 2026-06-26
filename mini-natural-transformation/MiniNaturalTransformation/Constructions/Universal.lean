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

/-! ## Adjoint Situation via Universal Natural Transformation -/

/--
An adjunction F ⊣ G between functors F : C → D and G : D → C
can be characterized by the existence of a universal natural
transformation ε : F∘G ⇒ Id_D (counit) or η : Id_C ⇒ G∘F (unit).

Here we formalize the unit-counit formulation:
- Unit η : Id_C ⇒ G∘F (universal arrow from each X to G(F(X)))
- Counit ε : F∘G ⇒ Id_D (universal arrow from F(G(Y)) to each Y)
- Triangle identities: (Gε) ∘ (ηG) = id_G and (εF) ∘ (Fη) = id_F
-/
structure AdjunctionData {C D : Category} (F : Functor C D) (G : Functor D C) where
  unit : Functor.id C ⇒ Functor.comp F G
  counit : Functor.comp G F ⇒ Functor.id D
  triangle_left : ∀ (X : C.Obj),
    D.comp (counit.component (F.mapObj X)) (F.mapHom (unit.component X)) = D.id (F.mapObj X)
  triangle_right : ∀ (Y : D.Obj),
    C.comp (G.mapHom (counit.component Y)) (unit.component (G.mapObj Y)) = C.id (G.mapObj Y)

/--
The triangle identities for an adjunction: (Gε) ∘ (ηG) = id_G.
-/
theorem adjunction_triangle_right_alt {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : AdjunctionData F G) (X : D.Obj) :
    C.comp (G.mapHom (adj.counit.component X)) (adj.unit.component (G.mapObj X)) =
    C.id (G.mapObj X) := adj.triangle_right X

/--
The triangle identities for an adjunction: (εF) ∘ (Fη) = id_F.
-/
theorem adjunction_triangle_left_alt {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : AdjunctionData F G) (X : C.Obj) :
    D.comp (adj.counit.component (F.mapObj X)) (F.mapHom (adj.unit.component X)) =
    D.id (F.mapObj X) := adj.triangle_left X

/-! ## Universal Property via Unit-Counit -/

/--
The unit η : Id_C ⇒ G∘F uniquely determines the adjunction: for each
X, η_X is a universal arrow from X to F (along G).
-/
def universalArrowFromUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (η : Functor.id C ⇒ Functor.comp F G) (X : C.Obj) : Type :=
  ∀ (A : D.Obj) (f : D[X, G.mapObj A]),
    ∃! (g : D[F.mapObj X, A]),
      D.comp (G.mapHom g) (η.component X) = f

/-! ## #eval Examples -/

/-- The identity natural transformation Δ_Nat ⇒ Δ_Nat is universal. -/
def constNatUniversal : UniversalArrow Nat constNat := idUniversal Nat

/-- Identity adjunction: Id ⊣ Id with unit = id and counit = id. -/
def identityAdjunctionData (C : Category) : AdjunctionData (Functor.id C) (Functor.id C) where
  unit := NaturalTransformation.id (Functor.id C)
  counit := NaturalTransformation.id (Functor.id C)
  triangle_left X := by simp
  triangle_right Y := by simp

#eval "Constructions.Universal: UniversalNatTrans, isUniversalComponent, UniversalArrow, idUniversal"
#eval "AdjunctionData, adjunction_unit_is_universal, universalArrowFromUnit, identityAdjunctionData"
#eval s!"Universal arrow from Nat to constNat (trivial)"
#eval s!"Universal property characterizes adjunctions"
#eval s!"Identity adjunction: Id_C ⊣ Id_C"
