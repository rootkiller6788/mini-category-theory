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
An extranatural transformation generalizes dinatural transformations
to functors of mixed variance.
-/
structure ExtranaturalTransformation {C D : Category}
    (F : Functor ((Cᵒᵖ ×ᶜ Cᵒᵖ) ×ᶜ C) D) (G : Functor C D) where
  component : ∀ (X Y : C.Obj), D[F.mapObj ((X, X), Y), G.mapObj Y]
  extranatural : ∀ {X X' : C.Obj} (f : C[X, X']) (Y : C.Obj),
    D.comp (G.mapHom (C.id Y)) (component X Y) =
    D.comp (G.mapHom (C.id Y)) (component X' Y)

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

/-! ## #eval Examples -/

/-- A cartesian natural transformation from List to Option (head). -/
def headCartesian : CartesianNatTrans listFunctor maybeFunctor where
  components X xs := xs.head?
  natural {X Y} f xs := by
    simp

#eval "Properties.ClassificationData: isPointwise, CartesianNatTrans, DinaturalTransformation, ExtranaturalTransformation"
#eval s!"Cartesian natural transformation: head : List → Option"
#eval headCartesian.toNatTrans.component Nat [1,2,3]
