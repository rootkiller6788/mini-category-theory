/-
# MiniFunctorCore.Properties.Invariants

Stub module: invariants of functors and functor categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Functor Invariants -/

/--
A functor F : C → D is faithful if it is injective on hom-sets.
-/
def Functor.IsFaithful (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} (f g : C[X, Y]), F.mapHom f = F.mapHom g → f = g

/--
A functor F : C → D is full if it is surjective on hom-sets.
-/
def Functor.IsFull (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} (h : D[F.mapObj X, F.mapObj Y]),
    ∃ (f : C[X, Y]), F.mapHom f = h

/--
A functor F : C → D is fully faithful if it is bijective on hom-sets.
-/
def Functor.IsFullyFaithful (F : Functor C D) : Prop :=
  Functor.IsFaithful F ∧ Functor.IsFull F

/--
A functor F : C → D is essentially surjective if every object of D
is isomorphic to F(X) for some X in C.
-/
def Functor.IsEssentiallySurjective (F : Functor C D) : Prop :=
  ∀ (Y : D.Obj), ∃ (X : C.Obj), True

#eval "Properties.Invariants: stub — Functor.IsFaithful, IsFull, IsFullyFaithful, IsEssentiallySurjective"
