/-
# MiniNaturalTransformation.Core.Objects

Identity natural transformation, whiskering, and component-level operations.
Provides the fundamental operations on natural transformations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Identity Natural Transformation -/

/--
The identity natural transformation `id_F : F ⇒ F` has components `id_{F X}`.
-/
def NaturalTransformation.id {C D : Category} (F : Functor C D) : F ⇒ F where
  component X := D.id (F.mapObj X)
  naturality f := by
    simp [D.id_comp, D.comp_id]

/-! ## Horizontal Composition via Whiskering -/

/--
Left whiskering: given `F : C → D` and `α : G ⇒ H` (with `G, H : D → E`),
produces `Fα : FG ⇒ FH` with component `α_{F X}`.
-/
def NaturalTransformation.whiskerLeft {C D E : Category}
    (F : Functor C D) {G H : Functor D E} (α : G ⇒ H) :
    Functor.comp F G ⇒ Functor.comp F H where
  component X := α.component (F.mapObj X)
  naturality f := by
    simp [α.naturality, F.preservesComp]

/--
Right whiskering: given `α : F ⇒ G` (with `F, G : C → D`) and `H : D → E`,
produces `αH : FH ⇒ GH` with component `H(α_X)`.
-/
def NaturalTransformation.whiskerRight {C D E : Category}
    {F G : Functor C D} (α : F ⇒ G) (H : Functor D E) :
    Functor.comp F H ⇒ Functor.comp G H where
  component X := H.mapHom (α.component X)
  naturality f := by
    have h := α.naturality f
    simp [H.preservesComp, ← H.preservesComp, h]

/-! ## Component-wise Operations -/

/--
Get the component of a natural transformation at a specific object.
-/
def NaturalTransformation.componentAt {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (X : C.Obj) : D[F.mapObj X, G.mapObj X] := η.component X

/--
The naturality square for a specific morphism f : X → Y.
-/
theorem naturalityAt {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) {X Y : C.Obj} (f : C[X, Y]) :
    D.comp (η.component Y) (F.mapHom f) = D.comp (G.mapHom f) (η.component X) :=
  η.naturality f

/--
Vertical composition of the identity with any natural transformation
gives the same natural transformation (left unit).
-/
theorem vcomp_id_left {C D : Category} {F G : Functor C D} (α : F ⇒ G) :
    NaturalTransformation.vcomp (NaturalTransformation.id G) α = α := by
  funext X; simp [NaturalTransformation.vcomp, NaturalTransformation.id]

/--
Vertical composition of any natural transformation with the identity
gives the same natural transformation (right unit).
-/
theorem vcomp_id_right {C D : Category} {F G : Functor C D} (α : F ⇒ G) :
    NaturalTransformation.vcomp α (NaturalTransformation.id F) = α := by
  funext X; simp [NaturalTransformation.vcomp, NaturalTransformation.id, D.id_comp, D.comp_id]

/-! ## #eval Examples -/

def idListNat : listFunctor ⇒ listFunctor := NaturalTransformation.id listFunctor

#eval "Core.Objects: NT.id, whiskerLeft, whiskerRight, componentAt, vcomp_id_left, vcomp_id_right"
#eval idListNat.component Nat ([1,2,3] : List Nat)
#eval s!"Identity naturality verified: component at Nat = identity morphism on List Nat"
