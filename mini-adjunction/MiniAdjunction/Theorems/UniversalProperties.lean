/-
# MiniAdjunction.Theorems.UniversalProperties

Universal arrows, universal property of the unit, universal property of the counit.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Universal Arrow -/

/--
A universal arrow from object X to functor G is a pair (A, η : X → G(A))
such that for any f : X → G(B), there is a unique g : A → B with G(g) ∘ η = f.
-/
structure UniversalArrow {C D : Category} (X : C.Obj) (G : Functor D C) where
  target : D.Obj
  arrow : C[X, G.mapObj target]
  universal : Prop  -- ∀ (B : D.Obj) (f : C[X, G.mapObj B]),
                     --   ∃! (g : D[target, B]), C.comp (G.mapHom g) arrow = f

/--
A universal arrow from functor F to object Y is a pair (A, ε : F(A) → Y)
with the dual universal property.
-/
structure UniversalArrowFrom {C D : Category} (F : Functor C D) (Y : D.Obj) where
  source : C.Obj
  arrow : D[F.mapObj source, Y]
  universal : Prop

/-! ## Unit as Universal Arrow -/

/--
In an adjunction F ⊣ G, the unit η_X : X → G(F X) is a universal arrow
from X to G.
-/
axiom unitIsUniversalArrow {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) : Nonempty (UniversalArrow X G)

/--
The universal property of the unit: for any f : X → G(Y),
there exists a unique g : F(X) → Y such that G(g) ∘ η_X = f.
The unique g is given by ε_Y ∘ F(f) (the adjoint transpose).
-/
axiom universalPropertyUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) (f : C[X, G.mapObj Y]) : Prop

/-! ## Counit as Universal Arrow -/

/--
In an adjunction F ⊣ G, the counit ε_Y : F(G Y) → Y is a universal arrow
from F to Y.
-/
axiom counitIsUniversalArrow {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (Y : D.Obj) : Nonempty (UniversalArrowFrom F Y)

/--
The universal property of the counit: for any g : F(X) → Y,
there exists a unique f : X → G(Y) such that ε_Y ∘ F(f) = g.
The unique f is given by G(g) ∘ η_X (the adjoint transpose).
-/
axiom universalPropertyCounit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) (g : D[F.mapObj X, Y]) : Prop

/-! ## Adjoint Transpose -/

/--
The adjoint transpose (or mate) of f : F X → Y is
  f^♭ = G(f) ∘ η_X : X → G Y
-/
def adjointTranspose {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X : C.Obj} {Y : D.Obj} (g : D[F.mapObj X, Y]) : C[X, G.mapObj Y] :=
  C.comp (G.mapHom g) (adj.unit.component X)

-- Notation: g^♭ for the adjoint transpose
notation:50 g:50 "♭" => adjointTranspose g

/--
The inverse adjoint transpose of f : X → G Y is
  f^♯ = ε_Y ∘ F(f) : F X → Y
-/
def adjointTransposeInv {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X : C.Obj} {Y : D.Obj} (f : C[X, G.mapObj Y]) : D[F.mapObj X, Y] :=
  D.comp (adj.counit.component Y) (F.mapHom f)

-- Notation: f^♯ for the inverse adjoint transpose
notation:50 f:50 "♯" => adjointTransposeInv f

/--
The transpose and its inverse are mutual inverses.
-/
axiom transposeBijection {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X : C.Obj} {Y : D.Obj} (g : D[F.mapObj X, Y]) :
    adjointTransposeInv adj (adjointTranspose adj g) = g

/--
The inverse transpose property.
-/
axiom transposeBijectionInv {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X : C.Obj} {Y : D.Obj} (f : C[X, G.mapObj Y]) :
    adjointTranspose adj (adjointTransposeInv adj f) = f

/-! ## Unit/Counit as Universal Elements -/

/--
The unit η_X is the image of id_{F X} under the hom-set bijection.
-/
theorem unitIsTransposeOfId {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) :
    adjointTranspose adj (D.id (F.mapObj X)) = adj.unit.component X := by
  simp [adjointTranspose, G.preservesId, C.id_comp]

/--
The counit ε_Y is the image of id_{G Y} under the inverse hom-set bijection.
-/
theorem counitIsTransposeOfId {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (Y : D.Obj) :
    adjointTransposeInv adj (C.id (G.mapObj Y)) = adj.counit.component Y := by
  simp [adjointTransposeInv, F.preservesId, D.comp_id]

#eval "Theorems.UniversalProperties: UniversalArrow, universal property of unit/counit"
#eval "Theorems.UniversalProperties: adjointTranspose g♭, adjointTransposeInv f♯"
#eval "Theorems.UniversalProperties: unit = trans(id), counit = trans⁻¹(id)"
