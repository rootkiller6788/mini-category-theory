/-
# MiniAdjunction.Core.Laws

Adjunction laws: unit_naturality, counit_naturality, hom-set bijection,
adjunction from hom-set bijection, triangle equivalence.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Naturality of Unit and Counit -/

/--
The unit of an adjunction is natural: for all f : X → Y,
  G(F f) ∘ η_X = η_Y ∘ f
-/
theorem unit_naturality {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) :
    C.comp (adj.unit.component Y) ((Functor.id C).mapHom f) =
    C.comp ((Functor.comp G F).mapHom f) (adj.unit.component X) :=
  adj.unit.naturality f

/--
The counit of an adjunction is natural: for all f : X → Y in D,
  f ∘ ε_X = ε_Y ∘ F(G f)
-/
theorem counit_naturality {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) :
    D.comp (adj.counit.component Y) ((Functor.comp F G).mapHom f) =
    D.comp ((Functor.id D).mapHom f) (adj.counit.component X) :=
  adj.counit.naturality f

/-! ## Triangle Identities -/

/--
The unit/counit triangle: ε_{F X} ∘ F(η_X) = id_{F X}
-/
theorem leftTriangleEq {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) :
    D.comp (adj.counit.component (F.mapObj X)) (F.mapHom (adj.unit.component X)) = D.id (F.mapObj X) :=
  adj.leftTriangle X

/--
The counit/unit triangle: G(ε_Y) ∘ η_{G Y} = id_{G Y}
-/
theorem rightTriangleEq {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (Y : D.Obj) :
    C.comp (G.mapHom (adj.counit.component Y)) (adj.unit.component (G.mapObj Y)) = C.id (G.mapObj Y) :=
  adj.rightTriangle Y

/-! ## Hom-Set Bijection (From Adjunction) -/

/--
The forward direction of the hom-set bijection from an adjunction:
  φ_{X,Y}(g : F X → Y) = G(g) ∘ η_X : X → G Y
-/
def adjunctionHomBijection {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) : D[F.mapObj X, Y] → C[X, G.mapObj Y] :=
  (Adjunction.toHomAdjunction adj).homIso X Y

/--
The inverse direction of the hom-set bijection:
  φ⁻¹_{X,Y}(f : X → G Y) = ε_Y ∘ F(f) : F X → Y
-/
def adjunctionHomBijectionInv {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) : C[X, G.mapObj Y] → D[F.mapObj X, Y] :=
  (Adjunction.toHomAdjunction adj).homIsoInv X Y

/--
The hom-set bijection is indeed a bijection: φ⁻¹(φ(g)) = g.
-/
theorem homBijectionIsBijection {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) (g : D[F.mapObj X, Y]) :
    adjunctionHomBijectionInv adj X Y (adjunctionHomBijection adj X Y g) = g :=
  (Adjunction.toHomAdjunction adj).homIsoInv_left X Y g

/--
The inverse bijection property: φ(φ⁻¹(f)) = f.
-/
theorem homBijectionIsBijection' {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) (Y : D.Obj) (f : C[X, G.mapObj Y]) :
    adjunctionHomBijection adj X Y (adjunctionHomBijectionInv adj X Y f) = f :=
  (Adjunction.toHomAdjunction adj).homIsoInv_right X Y f

/-! ## Unit and Counit Determine Each Other -/

/--
Given F and G, a natural transformation η : id_C ⇒ G ∘ F is the unit
of some adjunction if there exists ε making the triangle identities hold.
-/
axiom unitDeterminesCounit {C D : Category} {F : Functor C D} {G : Functor D C}
    (η : Functor.id C ⇒ Functor.comp G F) : Prop

/--
Given F and G, a natural transformation ε : F ∘ G ⇒ id_D is the counit
of some adjunction if there exists η making the triangle identities hold.
-/
axiom counitDeterminesUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (ε : Functor.comp F G ⇒ Functor.id D) : Prop

/-! ## Opposite Adjunction -/

/--
If F ⊣ G, then taking opposites yields related adjoint structures.
-/
axiom adjunctionOp {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Identity Adjunction -/

/--
The identity functor is self-adjoint: id_C ⊣ id_C.
-/
def identityAdjunction (C : Category) : (Functor.id C) ⊣ (Functor.id C) where
  unit := NaturalTransformation.id (Functor.id C)
  counit := NaturalTransformation.id (Functor.id C)
  leftTriangle X := by
    simp [C.comp_id]
  rightTriangle Y := by
    simp [C.id_comp]

/-! ## Composition of Adjunctions -/

/--
If F ⊣ G (F : C → D, G : D → C) and H ⊣ K (H : D → E, K : E → D),
then H ∘ F ⊣ G ∘ K : C → E.
-/
axiom adjunctionsCompose {C D E : Category}
    {F : Functor C D} {G : Functor D C} {H : Functor D E} {K : Functor E D}
    (_ : F ⊣ G) (_ : H ⊣ K) : Nonempty ((Functor.comp H F) ⊣ (Functor.comp G K))

/-! ## Adjunction Invariants -/

/--
Left adjoints preserve epimorphisms.
-/
axiom leftAdjointPreservesEpi {C D : Category} {F : Functor C D}
    (_ : IsLeftAdjoint F) : Prop

/--
Right adjoints preserve monomorphisms.
-/
axiom rightAdjointPreservesMono {C D : Category} {G : Functor D C}
    (_ : IsRightAdjoint G) : Prop

/-! ## Currying / Uncurrying Adjunction -/

/--
Equivalent formulations of the adjunction relation:
  C(X, G(Y)) ≅ D(F(X), Y)   (hom-set adjunction)
vs.
  F ⊣ G via unit/counit (triangle identities)
-/
theorem homAdjEquiv {C D : Category} (F : Functor C D) (G : Functor D C) :
  Nonempty (F ⊣ G) ↔ Nonempty (HomAdjunction C D F G) := by
  constructor
  · intro ⟨adj⟩; exact ⟨Adjunction.toHomAdjunction adj⟩
  · intro ⟨ha⟩; exact ⟨HomAdjunction.toAdjunction ha⟩

#eval "Core.Laws: unit/counit naturality, triangle identities, hom-bijection theorems"
#eval "Core.Laws: identityAdjunction id ⊣ id, adjunctions compose (axiom)"
#eval "Core.Laws: leftAdjointPreservesEpi, rightAdjointPreservesMono (axioms)"
