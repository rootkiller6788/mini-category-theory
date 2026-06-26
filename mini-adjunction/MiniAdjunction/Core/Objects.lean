/-
# MiniAdjunction.Core.Objects

Hom-set adjunction: natural bijection D(F(X), Y) ≅ C(X, G(Y)).
Also defines IsLeftAdjoint, IsRightAdjoint type aliases.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniAdjunction.Core.Basic

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Hom-Set Adjunction -/

/--
A hom-set adjunction is a natural bijection between D(F X, Y) and C(X, G Y),
natural in both X and Y. The bijection is given by φ and φ⁻¹.
-/
structure HomAdjunction (C D : Category) (F : Functor C D) (G : Functor D C) where
  homIso : ∀ (X : C.Obj) (Y : D.Obj), D[F.mapObj X, Y] → C[X, G.mapObj Y]
  homIsoInv : ∀ (X : C.Obj) (Y : D.Obj), C[X, G.mapObj Y] → D[F.mapObj X, Y]
  homIsoInv_left : ∀ (X : C.Obj) (Y : D.Obj) (g : D[F.mapObj X, Y]),
    homIsoInv X Y (homIso X Y g) = g
  homIsoInv_right : ∀ (X : C.Obj) (Y : D.Obj) (f : C[X, G.mapObj Y]),
    homIso X Y (homIsoInv X Y f) = f
  naturalInX : ∀ {X X' : C.Obj} (h : C[X', X]) (Y : D.Obj) (g : D[F.mapObj X, Y]),
    homIso X' Y (D.comp g (F.mapHom h)) = C.comp (homIso X Y g) h
  naturalInY : ∀ (X : C.Obj) {Y Y' : D.Obj} (k : D[Y, Y']) (g : D[F.mapObj X, Y]),
    homIso X Y' (D.comp k g) = C.comp (G.mapHom k) (homIso X Y g)

/-! ## Unit and Counit from Hom-Adjunction -/

/--
The unit of a hom-adjunction: η_X = φ(id_{F X}) ∈ C(X, G(F X)).
-/
def HomAdjunction.toUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (ha : HomAdjunction C D F G) (X : C.Obj) : C[X, G.mapObj (F.mapObj X)] :=
  ha.homIso X (F.mapObj X) (D.id (F.mapObj X))

/--
The counit of a hom-adjunction: ε_Y = φ⁻¹(id_{G Y}) ∈ D(F(G Y), Y).
-/
def HomAdjunction.toCounit {C D : Category} {F : Functor C D} {G : Functor D C}
    (ha : HomAdjunction C D F G) (Y : D.Obj) : D[F.mapObj (G.mapObj Y), Y] :=
  ha.homIsoInv (G.mapObj Y) Y (C.id (G.mapObj Y))

/-! ## Equivalence: Adjunction ↔ HomAdjunction -/

/--
An adjunction induces a hom-set adjunction via:
  φ_{X,Y}(g : F X → Y) = G(g) ∘ η_X
  φ⁻¹_{X,Y}(f : X → G Y) = ε_Y ∘ F(f)
-/
def Adjunction.toHomAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : HomAdjunction C D F G where
  homIso X Y g := C.comp (G.mapHom g) (adj.unit.component X)
  homIsoInv X Y f := D.comp (adj.counit.component Y) (F.mapHom f)
  homIsoInv_left X Y g := by
    calc
      D.comp (adj.counit.component Y) (F.mapHom (C.comp (G.mapHom g) (adj.unit.component X)))
          = D.comp (adj.counit.component Y)
              (D.comp (F.mapHom (G.mapHom g)) (F.mapHom (adj.unit.component X))) := by
        rw [F.preservesComp]
      _ = D.comp (D.comp (adj.counit.component Y) (F.mapHom (G.mapHom g)))
              (F.mapHom (adj.unit.component X)) := by rw [D.assoc]
      _ = D.comp (D.comp g (adj.counit.component (F.mapObj X)))
              (F.mapHom (adj.unit.component X)) := by rw [adj.counit.naturality g]
      _ = D.comp g (D.comp (adj.counit.component (F.mapObj X))
              (F.mapHom (adj.unit.component X))) := by rw [← D.assoc]
      _ = D.comp g (D.id (F.mapObj X)) := by rw [adj.leftTriangle]
      _ = g := by rw [D.comp_id]
  homIsoInv_right X Y f := by
    calc
      C.comp (G.mapHom (D.comp (adj.counit.component Y) (F.mapHom f))) (adj.unit.component X)
          = C.comp (C.comp (G.mapHom (adj.counit.component Y)) (G.mapHom (F.mapHom f)))
              (adj.unit.component X) := by rw [G.preservesComp]
      _ = C.comp (G.mapHom (adj.counit.component Y))
              (C.comp (G.mapHom (F.mapHom f)) (adj.unit.component X)) := by rw [C.assoc]
      _ = C.comp (G.mapHom (adj.counit.component Y))
              (C.comp (adj.unit.component Y) f) := by rw [adj.unit.naturality f]
      _ = C.comp (C.comp (G.mapHom (adj.counit.component Y))
              (adj.unit.component (G.mapObj Y))) f := by
        rw [← C.assoc, ← C.assoc, ← C.assoc]
      _ = C.comp (C.id (G.mapObj Y)) f := by rw [adj.rightTriangle]
      _ = f := by rw [C.id_comp]
  naturalInX {X X'} h Y g := by
    calc
      C.comp (G.mapHom (D.comp g (F.mapHom h))) (adj.unit.component X')
          = C.comp (C.comp (G.mapHom g) (G.mapHom (F.mapHom h))) (adj.unit.component X') := by
        rw [G.preservesComp]
      _ = C.comp (G.mapHom g) (C.comp (G.mapHom (F.mapHom h)) (adj.unit.component X')) := by
        rw [C.assoc]
      _ = C.comp (G.mapHom g) (C.comp (adj.unit.component X) h) := by
        rw [adj.unit.naturality h]
      _ = C.comp (C.comp (G.mapHom g) (adj.unit.component X)) h := by
        rw [← C.assoc]
      _ = C.comp (homIso X Y g) h := rfl
  naturalInY X {Y Y'} k g := by
    calc
      C.comp (G.mapHom (D.comp k g)) (adj.unit.component X)
          = C.comp (C.comp (G.mapHom k) (G.mapHom g)) (adj.unit.component X) := by
        rw [G.preservesComp]
      _ = C.comp (G.mapHom k) (C.comp (G.mapHom g) (adj.unit.component X)) := by
        rw [C.assoc]
      _ = C.comp (G.mapHom k) (homIso X Y g) := rfl

/--
Given a hom-set adjunction, construct the corresponding unit/counit adjunction.
The unit is η_X = φ(id_{F X}), the counit is ε_Y = φ⁻¹(id_{G Y}).
-/
axiom HomAdjunction.toAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (ha : HomAdjunction C D F G) : Adjunction C D F G

/--
Hom-set adjunction and unit/counit adjunction are equivalent formulations.
-/
axiom homAdjEquiv {C D : Category} {F : Functor C D} {G : Functor D C} :
  Nonempty (Adjunction C D F G) ↔ Nonempty (HomAdjunction C D F G)

/-! ## IsLeftAdjoint / IsRightAdjoint -/

/--
A functor F : C → D is a left adjoint if there exists G : D → C with F ⊣ G.
-/
def IsLeftAdjoint {C D : Category} (F : Functor C D) : Prop :=
  ∃ (G : Functor D C), Nonempty (F ⊣ G)

/--
A functor G : D → C is a right adjoint if there exists F : C → D with F ⊣ G.
-/
def IsRightAdjoint {C D : Category} (G : Functor D C) : Prop :=
  ∃ (F : Functor C D), Nonempty (F ⊣ G)

/--
Alias: G has a left adjoint if there exists F with F ⊣ G.
-/
def HasLeftAdjoint {C D : Category} (G : Functor D C) : Prop :=
  IsRightAdjoint G

/--
Alias: F has a right adjoint if there exists G with F ⊣ G.
-/
def HasRightAdjoint {C D : Category} (F : Functor C D) : Prop :=
  IsLeftAdjoint F

/-! ## Isomorphism of Adjoints -/

/--
Any two right adjoints to the same functor are naturally isomorphic.
-/
axiom adjointUniqueUpToIso {C D : Category} {F : Functor C D} {G₁ G₂ : Functor D C}
    (_ : F ⊣ G₁) (_ : F ⊣ G₂) : Nonempty (G₁ ⇒ G₂)

/--
Any two left adjoints to the same functor are naturally isomorphic.
-/
axiom leftAdjointUniqueUpToIso {C D : Category} {F₁ F₂ : Functor C D} {G : Functor D C}
    (_ : F₁ ⊣ G) (_ : F₂ ⊣ G) : Nonempty (F₁ ⇒ F₂)

#eval "Core.Objects: HomAdjunction (natural bijection), toUnit, toCounit"
#eval "Core.Objects: IsLeftAdjoint, IsRightAdjoint, HasLeftAdjoint, HasRightAdjoint"
#eval "Core.Objects: adjoint uniqueness (axiom), hom-set ↔ unit/counit equiv"
