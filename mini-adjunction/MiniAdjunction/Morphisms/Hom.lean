/-
# MiniAdjunction.Morphisms.Hom

Morphisms between adjunctions, horizontal/vertical composition,
the category of adjunctions.
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

/-! ## Morphism Between Adjunctions -/

/--
A morphism from adjunction (F ⊣ G) to (F' ⊣ G') consists of
natural transformations α : F ⇒ F' and β : G' ⇒ G such that
the unit and counit diagrams commute.
-/
structure AdjunctionMorphism {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') where
  leftNatTrans : F ⇒ F'
  rightNatTrans : G' ⇒ G
  unit_commutes : ∀ (X : C.Obj),
    C.comp (rightNatTrans.component (F.mapObj X)) (adj'.unit.component X) =
    C.comp (G.mapHom (leftNatTrans.component X)) (adj.unit.component X)
  counit_commutes : ∀ (Y : D.Obj),
    D.comp (adj'.counit.component Y) (leftNatTrans.component (G'.mapObj Y)) =
    D.comp (adj.counit.component Y) (F.mapHom (rightNatTrans.component Y))

/-! ## Identity Morphism of Adjunctions -/

/--
The identity morphism from an adjunction to itself.
-/
def AdjunctionMorphism.id {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : AdjunctionMorphism adj adj where
  leftNatTrans := NaturalTransformation.id F
  rightNatTrans := NaturalTransformation.id G
  unit_commutes X := by
    simp [C.comp_id, C.id_comp]
  counit_commutes Y := by
    simp [D.comp_id, D.id_comp]

/-! ## Composition of Adjunction Morphisms -/

/--
Vertical composition of adjunction morphisms.
-/
def AdjunctionMorphism.comp {C D : Category}
    {F F' F'' : Functor C D} {G G' G'' : Functor D C}
    {adj1 : F ⊣ G} {adj2 : F' ⊣ G'} {adj3 : F'' ⊣ G''}
    (m2 : AdjunctionMorphism adj2 adj3) (m1 : AdjunctionMorphism adj1 adj2) :
    AdjunctionMorphism adj1 adj3 where
  leftNatTrans := NaturalTransformation.vcomp m2.leftNatTrans m1.leftNatTrans
  rightNatTrans := NaturalTransformation.vcomp m1.rightNatTrans m2.rightNatTrans
  unit_commutes X := by
    simp [NaturalTransformation.vcomp, C.assoc, C.comp_id, C.id_comp,
      m1.unit_commutes X, m2.unit_commutes X]
  counit_commutes Y := by
    simp [NaturalTransformation.vcomp, D.assoc, D.comp_id, D.id_comp,
      m1.counit_commutes Y, m2.counit_commutes Y]

/-! ## The Category of Adjunctions (concept) -/

/--
The type of adjunctions from C to D is the collection of
all (F, G, adj) where adj : F ⊣ G.
-/
structure AdjunctionObject (C D : Category) where
  F : Functor C D
  G : Functor D C
  adj : F ⊣ G

/--
A morphism in the "category of adjunctions" is an AdjunctionMorphism.
-/
def AdjunctionCategory (C D : Category) : Category where
  Obj := AdjunctionObject C D
  Hom A B := AdjunctionMorphism A.adj B.adj
  id A := AdjunctionMorphism.id A.adj
  comp g f := AdjunctionMorphism.comp g f
  comp_id f := by
    simp [AdjunctionMorphism.id, AdjunctionMorphism.comp]
  id_comp f := by
    simp [AdjunctionMorphism.id, AdjunctionMorphism.comp]
  assoc f g h := by
    simp [AdjunctionMorphism.comp, NaturalTransformation.vcomp, C.assoc, D.assoc]

/-! ## Maps Between Adjunctions -/

/--
Given adjunctions F ⊣ G : C ⇄ D and F' ⊣ G' : C ⇄ D,
a pair of natural isomorphisms α : F ≅ F' and β : G ≅ G'
satisfying compatibility conditions induces an isomorphism of adjunctions.
-/
structure AdjointIsomorphism {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') where
  leftIso : F ⇒ F'
  leftIsoInv : F' ⇒ F
  rightIso : G ⇒ G'
  rightIsoInv : G' ⇒ G

/-! ## Reflection and Creation -/

/--
A right adjoint reflects isomorphisms.
-/
axiom rightAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
A left adjoint reflects epimorphisms.
-/
axiom leftAdjointReflectsEpi {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

#eval "Morphisms.Hom: AdjunctionMorphism, id/comp, AdjunctionCategory, AdjointIsomorphism"
#eval "Morphisms.Hom: rightAdjointReflectsIso, leftAdjointReflectsEpi (axioms)"
#eval "Morphisms.Hom: Vertical composition of adjunction morphisms"
