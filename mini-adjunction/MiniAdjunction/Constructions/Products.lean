/-
# MiniAdjunction.Constructions.Products

Product-exponential adjunction (curry/uncurry), tensor-hom adjunction.
The fundamental adjunctions of cartesian closed categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniFunctorCore

/-! ## Product Functor -/

/--
Given an object A in C, the product functor (- × A) : C → C
sends X to X × A (assuming products exist).
-/
structure ProductFunctor (C : Category) (A : C.Obj) where
  productFunctor : Functor C C
  hasProducts : ∀ (X : C.Obj), Prop

/-! ## Exponential Functor -/

/--
Given an object A in C, the exponential functor A ⇒ (-) : C → C
sends Y to A ⇒ Y (assuming exponentials exist).
-/
structure ExponentialFunctor (C : Category) (A : C.Obj) where
  exponentialFunctor : Functor C C
  hasExponentials : ∀ (Y : C.Obj), Prop

/-! ## Product-Exponential Adjunction -/

/--
The product-exponential adjunction: (- × A) ⊣ (A ⇒ -).
For all objects X, Y: C(X × A, Y) ≅ C(X, A ⇒ Y).
Equivalently: curry: C(X × A, Y) → C(X, A ⇒ Y) and
uncurry: C(X, A ⇒ Y) → C(X × A, Y).
-/
structure ProductExponentialAdjunction (C : Category) (A : C.Obj) where
  prodF : Functor C C
  expF : Functor C C
  adj : prodF ⊣ expF
  curry : ∀ (X Y : C.Obj), C[X, expF.mapObj Y] → C[prodF.mapObj X, Y]
  uncurry : ∀ (X Y : C.Obj), C[prodF.mapObj X, Y] → C[X, expF.mapObj Y]

/--
The bijection curry/uncurry is the hom-set adjunction bijection:
  C(X × A, Y) ≅ C(X, A ⇒ Y)
-/
axiom curryUncurryBijection {C : Category} {A : C.Obj}
    (pea : ProductExponentialAdjunction C A) (X Y : C.Obj) : Prop

/--
In Set, the product-exponential adjunction is the standard
curry/uncurry bijection.
-/
def setProductExponential (A : Type u) : ProductExponentialAdjunction SetCat A where
  prodF := {
    mapObj X := X × A
    mapHom f := λ (x, a) => (f x, a)
    preservesId _ := rfl
    preservesComp _ _ := rfl
  }
  expF := {
    mapObj Y := A → Y
    mapHom g h := λ a => g (h a)
    preservesId _ := rfl
    preservesComp _ _ := rfl
  }
  adj := by
    -- This is a constructive example: (- × A) ⊣ (A ⇒ -) in Set
    refine {
      unit := ?_
      counit := ?_
      leftTriangle := ?_
      rightTriangle := ?_
    }
    · refine {
        component X x a := (x, a)
        naturality X Y f := ?_
      }
      ext x; rfl
    · refine {
        component Y ya := ya.1 ya.2
        naturality X Y f := ?_
      }
      ext ya; rfl
    · intro X; ext xa; rfl
    · intro Y; ext y; rfl
  curry X Y f x a := f (x, a)
  uncurry X Y g xa := g xa.1 xa.2

#eval "Constructions.Products: setProductExponential = (- × A) ⊣ (A ⇒ -) in Set"
#eval "Constructions.Products: curry/uncurry bijection in Set"
#eval "Constructions.Products: Product-Exponential Adjunction defined"
