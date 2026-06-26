/-
# MiniFunctorCore.Morphisms.Hom

Functor homomorphisms — morphisms between functor-related objects.
Natural transformations as morphisms in the functor category.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Identity Natural Transformation -/

/--
The identity natural transformation on a functor F.
-/
def NatTrans.id {C D : Category} (F : Functor C D) : F ⇒ F where
  component X := D.id (F.mapObj X)
  naturality f := by simp

/-! ## Natural Transformation Composition Types -/

/--
Vertical composition of natural transformations (vertical ``∘'').
-/
def NatTrans.vcomp {C D : Category} {F G H : Functor C D}
    (β : G ⇒ H) (α : F ⇒ G) : F ⇒ H :=
  NaturalTransformation.vcomp β α

infixr:80 " ⊚ " => NatTrans.vcomp

/--
Horizontal composition of natural transformations (horizontal ``∘'').
-/
def NatTrans.hcomp {B C D : Category}
    {F G : Functor B C} {H K : Functor C D}
    (α : H ⇒ K) (β : F ⇒ G) : Functor.comp H F ⇒ Functor.comp K G :=
  NaturalTransformation.hcomp α β

infixr:70 " ⊛ " => NatTrans.hcomp

/-! ## Category of Endofunctors -/

/--
The category of endofunctors on C: objects are functors C → C,
morphisms are natural transformations.
-/
def EndofunctorCategory (C : Category) : Category := [C, C]

/-! ## Functor Precomposition -/

/--
Precomposition with a functor F : B → C gives a functor
F* : [C, D] → [B, D].
-/
def precomposition {B C D : Category} (F : Functor B C) :
    Functor ([C, D]) ([B, D]) where
  mapObj G := Functor.comp G F
  mapHom {G H} α :=
    let comp : G ⇒ H := α
    { component X := comp.component (F.mapObj X)
      naturality f := by
        simpa using congrArg (fun t => t) (comp.naturality (F.mapHom f)) }
  preservesId G := by
    funext X; rfl
  preservesComp β α := by
    funext X; rfl

/-! ## Functor Postcomposition -/

/--
Postcomposition with a functor G : C → D gives a functor
G* : [B, C] → [B, D].
-/
def postcomposition {B C D : Category} (G : Functor C D) :
    Functor ([B, C]) ([B, D]) where
  mapObj F := Functor.comp G F
  mapHom {F H} α :=
    { component X := G.mapHom (α.component X)
      naturality f := by
        simp [G.preservesComp, α.naturality] }
  preservesId F := by
    funext X; simp [G.preservesId]
  preservesComp β α := by
    funext X; simp [G.preservesComp]

/-! ## Whiskering -/

/--
Left whiskering: given β : G ⇒ H and a functor F, produce
Fβ : FG ⇒ FH.
-/
def whiskerLeft {B C D : Category} (F : Functor B C)
    {G H : Functor C D} (β : G ⇒ H) : Functor.comp G F ⇒ Functor.comp H F where
  component X := β.component (F.mapObj X)
  naturality f := by
    simpa using congrArg id (β.naturality (F.mapHom f))

/--
Right whiskering: given α : F ⇒ G and a functor H, produce
αH : FH ⇒ GH.
-/
def whiskerRight {B C D : Category} {F G : Functor B C}
    (α : F ⇒ G) (H : Functor C D) : Functor.comp H F ⇒ Functor.comp H G where
  component X := H.mapHom (α.component X)
  naturality f := by
    simp [H.preservesComp, α.naturality]

/-! ## Composition with Hom-Functor -/

/--
Composition with a fixed morphism on the left gives a natural
transformation between hom-functors.
-/
def homMapLeft {C : Category} {X Y : C.Obj} (f : C[X, Y]) (Z : C.Obj) :
    SetCat[homFunctor C Y | Z, homFunctor C X | Z] :=
  fun g => C.comp g f

def homMapRight {C : Category} {X Y : C.Obj} (f : C[X, Y]) (Z : C.Obj) :
    SetCat[homFunctor C Z | X, homFunctor C Z | Y] :=
  fun g => C.comp f g

#eval "Morphisms.Hom: NatTrans.id, vcomp (⊚), hcomp (⊛), EndofunctorCategory, precomposition, postcomposition, whiskerLeft, whiskerRight, homMapLeft, homMapRight"
