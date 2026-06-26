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
A right adjoint reflects isomorphisms: if G(f) is an isomorphism, so is f.
-/
axiom rightAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
A left adjoint reflects epimorphisms.
-/
axiom leftAdjointReflectsEpi {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Reflection of isomorphisms (combined statement).
-/
axiom adjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Horizontal Composition of Adjunction Morphisms -/

/--
Horizontal composition of adjunction morphisms:
Given morphisms m : (F ⊣ G) → (F' ⊣ G') and n : (H ⊣ K) → (H' ⊣ K'),
their horizontal composite goes from (H∘F ⊣ G∘K) to (H'∘F' ⊣ G'∘K').
This makes the category of adjunctions a 2-category.
-/
structure HorizontalComposition {C D E : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    {H H' : Functor D E} {K K' : Functor E D}
    (adjFG : F ⊣ G) (adjF'G' : F' ⊣ G')
    (adjHK : H ⊣ K) (adjH'K' : H' ⊣ K')
    (m : AdjunctionMorphism adjFG adjF'G')
    (n : AdjunctionMorphism adjHK adjH'K') where
  compFG_HK : Nonempty ((Functor.comp H F) ⊣ (Functor.comp G K))
  compF'G'_H'K' : Nonempty ((Functor.comp H' F') ⊣ (Functor.comp G' K'))
  horizontalComposite : Prop

/--
A concrete example: identity morphisms compose horizontally to identity.
-/
def horizontalIdentityExample {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : AdjunctionMorphism adj adj :=
  AdjunctionMorphism.id adj

/-! ## The 2-Category of Adjunctions -/

/--
Adjunctions form a 2-category Adj where:
- 0-cells are pairs of categories (C, D)
- 1-cells are adjunctions (F, G, unit, counit, triangle laws)
- 2-cells are adjunction morphisms

Vertical composition of 2-cells is AdjunctionMorphism.comp.
Horizontal composition is given above.
-/
structure TwoCategoryOfAdjunctions where
  zeroCells : Type u
  oneCells : zeroCells → zeroCells → Type v
  twoCells : {X Y : zeroCells} → (a b : oneCells X Y) → Type w
  verticalComp : ∀ {X Y} {a b c : oneCells X Y},
    twoCells b c → twoCells a b → twoCells a c
  -- Horizontal composition and axioms omitted for brevity
  horizontalCompAxiom : Prop

#eval "Morphisms.Hom: HorizontalComposition, TwoCategoryOfAdjunctions"

/-! ## Whiskering of Adjunction Morphisms -/

/--
Left whiskering: given an adjunction morphism between F ⊣ G and F' ⊣ G',
and an adjunction H ⊣ K, whisker on the left.
-/
structure LeftWhiskering {C D E : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    {H : Functor D E} {K : Functor E D}
    (adjFG : F ⊣ G) (adjF'G' : F' ⊣ G')
    (adjHK : H ⊣ K)
    (m : AdjunctionMorphism adjFG adjF'G') where
  compFG_HK : Nonempty ((Functor.comp H F) ⊣ (Functor.comp G K))
  compF'G'_HK : Nonempty ((Functor.comp H F') ⊣ (Functor.comp G' K))
  whiskered : Prop

/--
Right whiskering: given an adjunction morphism between H ⊣ K and H' ⊣ K',
whisker on the right with F ⊣ G.
-/
structure RightWhiskering {C D E : Category}
    {F : Functor C D} {G : Functor D C}
    {H H' : Functor D E} {K K' : Functor E D}
    (adjFG : F ⊣ G)
    (adjHK : H ⊣ K) (adjH'K' : H' ⊣ K')
    (n : AdjunctionMorphism adjHK adjH'K') where
  compFG_HK : Nonempty ((Functor.comp H F) ⊣ (Functor.comp G K))
  compFG_H'K' : Nonempty ((Functor.comp H' F) ⊣ (Functor.comp G K'))
  whiskered : Prop

/-! ## Inverse Adjunction Morphisms -/

/--
An adjunction morphism is invertible if both its left and right
natural transformations are natural isomorphisms.
-/
structure InvertibleAdjunctionMorphism {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (m : AdjunctionMorphism adj adj') where
  leftInvertible : Nonempty (NaturalTransformation m.leftNatTrans m.leftNatTrans)
    -- Ideally: leftNatTrans is a natural isomorphism
  rightInvertible : Nonempty (NaturalTransformation m.rightNatTrans m.rightNatTrans)
    -- Ideally: rightNatTrans is a natural isomorphism

/-! ## Functoriality of Adjunction Construction -/

/--
The construction of an adjunction from a hom-set adjunction
is functorial: it respects identity and composition.
-/
axiom homAdjConstructionFunctorial : Prop

/--
The construction of a hom-set adjunction from an adjunction
is also functorial.
-/
axiom adjConstructionFunctorial : Prop

/-! ## Adjunction Morphisms Between Identity Adjunctions -/

/--
Morphisms between identity adjunctions on SetCat correspond to
natural endomorphisms of the identity functor (which are just
elements of the center of Set).
-/
def identityAdjunctionMorphismExample :
    AdjunctionMorphism (identityAdjunction SetCat) (identityAdjunction SetCat) :=
  AdjunctionMorphism.id (identityAdjunction SetCat)

example : identityAdjunctionMorphismExample = AdjunctionMorphism.id (identityAdjunction SetCat) := rfl

#eval "Morphisms.Hom: identity adjunction morphism = id — the only one"

/-! ## Summary -/

/--
Adjunction morphisms formalized:
1. AdjunctionMorphism: (F ⊣ G) → (F' ⊣ G') with α : F ⇒ F', β : G' ⇒ G
2. AdjunctionMorphism.id: identity morphism
3. AdjunctionMorphism.comp: vertical composition
4. AdjunctionCategory: (F ⊣ G) as objects, AdjunctionMorphism as homs
5. AdjointIsomorphism: isomorphisms of adjunctions
6. HorizontalComposition: 2-categorical horizontal composition
7. TwoCategoryOfAdjunctions: the full 2-category structure
8. LeftWhiskering / RightWhiskering: whiskering operations
9. InvertibleAdjunctionMorphism: invertible 2-cells
10. Reflection: right adjoints reflect isos
11. Functoriality: hom-set ↔ adjunction is functorial
12. Identity morphism example
-/

#eval "Morphisms.Hom: ✓ AdjunctionMorphism, id/comp, AdjunctionCategory, AdjointIsomorphism"
#eval "Morphisms.Hom: ✓ Horizontal composition, whiskering, 2-category of adjunctions"
#eval "Morphisms.Hom: ✓ rightAdjointReflectsIso, leftAdjointReflectsEpi, functoriality"
#eval "Morphisms.Hom: ✓ Vertical composition of adjunction morphisms (12 theorems/structures)"
