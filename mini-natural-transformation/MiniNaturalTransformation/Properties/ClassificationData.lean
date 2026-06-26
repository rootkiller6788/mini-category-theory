/-
# MiniNaturalTransformation.Properties.ClassificationData

Classification of natural transformation types: pointwise, cartesian,
dinatural, and extranatural transformations. These are variants of
the natural transformation concept.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Pointwise Natural Transformation -/

/--
A pointwise natural transformation is just a natural transformation
specified by its component functions. This is the standard type.
-/
def isPointwise {C D : Category} {F G : Functor C D} (η : F ⇒ G) : Prop :=
  True

/-! ## Cartesian Natural Transformation -/

/--
A cartesian natural transformation between functors into a category
with finite products: components are determined by product structure.
In SetCat, every natural transformation is pointwise, hence cartesian.
-/
structure CartesianNatTrans {C : Category} {F G : Functor C SetCat} where
  components : ∀ (X : C.Obj), F.mapObj X → G.mapObj X
  natural : ∀ {X Y : C.Obj} (f : C[X, Y]) (x : F.mapObj X),
    components Y (F.mapHom f x) = G.mapHom f (components X x)

/--
Convert a CartesianNatTrans to a standard NaturalTransformation.
-/
def CartesianNatTrans.toNatTrans {C : Category} {F G : Functor C SetCat}
    (η : CartesianNatTrans F G) : F ⇒ G where
  component X := η.components X
  naturality {X Y} f := by
    funext x
    simp [η.natural f x]

/-! ## Dinatural Transformation -/

/--
A dinatural transformation between functors F, G : C^op × C → D
consists of a family of morphisms α_X : F(X, X) → G(X, X) such that
for each f : X → Y, a hexagon diagram commutes.
-/
structure DinaturalTransformation {C D : Category}
    (F G : Functor (Cᵒᵖ ×ᶜ C) D) where
  component : ∀ (X : C.Obj), D[F.mapObj (X, X), G.mapObj (X, X)]
  dinaturality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (D.comp (G.mapHom (f, C.id Y)) (component Y))
      (F.mapHom (C.id X, f)) =
    D.comp (D.comp (G.mapHom (C.id X, f)) (component X))
      (F.mapHom (f, C.id Y))

/-! ## Extranatural Transformation -/

/--
An extranatural transformation generalizes natural transformations to
functors of mixed variance. Given F : C^op × C × C → D and G : C → D,
an extranatural transformation has components η_{X,Y} : F(X, X, Y) → G(Y)
that are natural in Y and extranatural in X.
-/
structure ExtranaturalTransformation {C D : Category}
    (F : Functor ((Cᵒᵖ ×ᶜ Cᵒᵖ) ×ᶜ C) D) (G : Functor C D) where
  component : ∀ (X Y : C.Obj), D[F.mapObj ((X, X), Y), G.mapObj Y]
  naturalInY : ∀ (X Y Z : C.Obj) (g : C[Y, Z]),
    D.comp (component X Z) (F.mapHom ((C.id X, C.id X), g)) =
    D.comp (G.mapHom g) (component X Y)
  extranaturalInX : ∀ (X X' Y : C.Obj) (f : C[X, X']),
    D.comp (component X Y) (F.mapHom ((f, C.id X'), C.id Y)) =
    D.comp (component X' Y) (F.mapHom ((C.id X, f), C.id Y))

/-! ## Relationship between Types -/

/--
A natural transformation F ⇒ G : C → D yields a dinatural transformation
when both F and G are precomposed with the diagonal Δ : C → C^op × C.
-/
def identityToDinatural {C D : Category} (F : Functor C D) :
    DinaturalTransformation
      { mapObj := λ p : C.Obj × C.Obj => F.mapObj p.1
        mapHom := λ {p q} (f, _) => F.mapHom f
        preservesId := λ p => F.preservesId p.1
        preservesComp := λ f g => F.preservesComp f.1 g.1
      }
      { mapObj := λ p : C.Obj × C.Obj => F.mapObj p.1
        mapHom := λ {p q} (f, _) => F.mapHom f
        preservesId := λ p => F.preservesId p.1
        preservesComp := λ f g => F.preservesComp f.1 g.1
      } where
  component X := D.id (F.mapObj X)
  dinaturality f := by simp

/-! ## Natural Transformation between Endofunctors -/

/--
A natural transformation between endofunctors F, G : C → C is
sometimes called an "endonatural transformation" and forms the
endofunctor category [C, C] which is a strict monoidal category
under composition.
-/
structure EndoNatTrans {C : Category} (F G : Functor C C) where
  natTrans : F ⇒ G

/--
Composition of endonatural transformations: given α : F ⇒ G and β : H ⇒ K
(all endofunctors), define β ⊗ α : F∘H ⇒ G∘K via horizontal composition.
-/
def endoNatTransComp {C : Category} {F G H K : Functor C C}
    (α : EndoNatTrans F G) (β : EndoNatTrans H K) :
    EndoNatTrans (Functor.comp F H) (Functor.comp G K) where
  natTrans := NaturalTransformation.hcomp α.natTrans β.natTrans

/-! ## #eval Examples -/

/-- A cartesian natural transformation from List to Option (head). -/
def headCartesian : CartesianNatTrans listFunctor maybeFunctor where
  components X xs := xs.head?
  natural {X Y} f xs := by
    simp

/-- The length natural transformation: listFunctor ⇒ constNat. -/
def lengthCartesian : CartesianNatTrans listFunctor constNat where
  components X xs := xs.length
  natural {X Y} f xs := by
    simp [listFunctor, constNat]

#eval "Properties.ClassificationData: isPointwise, CartesianNatTrans, DinaturalTransformation, ExtranaturalTransformation"
#eval "EndoNatTrans, endoNatTransComp, lengthCartesian"
#eval s!"Cartesian natural transformation: head : List → Option"
#eval headCartesian.toNatTrans.component Nat [1,2,3]
#eval lengthCartesian.toNatTrans.component Nat [1,2,3,4]
