/-
# MiniMorphismSystem.Morphisms.Hom

Properties of functors: full, faithful, essentially surjective.
The category of small categories Cat.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Properties of Functors -/

def Functor.IsFull {C D : Category} (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} (g : D[F.mapObj X, F.mapObj Y]),
    ∃ (f : C[X, Y]), F.mapHom f = g

def Functor.IsFaithful {C D : Category} (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} {f₁ f₂ : C[X, Y]}, F.mapHom f₁ = F.mapHom f₂ → f₁ = f₂

def Functor.IsFullyFaithful {C D : Category} (F : Functor C D) : Prop :=
  F.IsFull ∧ F.IsFaithful

def Functor.IsEssentiallySurjective {C D : Category} (F : Functor C D) : Prop :=
  ∀ (Y : D.Obj), ∃ (X : C.Obj), Nonempty (D[F.mapObj X, Y])

/-! ## The Category of Small Categories -/

def Cat : Category where
  Obj := Category
  Hom := Functor
  id := Functor.id
  comp G F := Functor.comp G F
  comp_id f := by
    cases f
    simp [Functor.id, Functor.comp]
  id_comp f := by
    cases f
    simp [Functor.id, Functor.comp]
  assoc f g h := by
    cases f; cases g; cases h
    simp [Functor.id, Functor.comp]

#eval "Morphisms.Hom: Full, Faithful, EssSurj, Cat category"
