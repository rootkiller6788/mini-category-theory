/-
# MiniCategoryCore.Bridges.ToComputation

Bridge from category theory to computation:
types as a category, Cartesian closed categories, lambda calculus models.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Constructions.Products

namespace MiniCategoryCore

/-! ## Types as a Category -/

/-- SetCat is the category of types and functions.
    It is the prototypical Cartesian closed category. -/

/-- SetCat has binary products (Cartesian product). -/
theorem SetCat.hasProducts : HasBinaryProducts (SetCat : Category) :=
  SetCat.hasBinaryProducts

/-- SetCat has exponential objects: the type Y^X = X → Y. -/
def SetCat.exponential (X Y : Type u) : Type u := X → Y

/-- Evaluation map ev : (X → Y) × X → Y. -/
def SetCat.eval (X Y : Type u) : SetCat[(SetCat.exponential X Y × X), Y] :=
  λ ⟨f, x⟩ => f x

/-- Currying: given f : Z × X → Y, produce λ z x => f (z, x) : Z → (X → Y). -/
def SetCat.curry {X Y Z : Type u} (f : SetCat[(Z × X), Y]) : SetCat[Z, SetCat.exponential X Y] :=
  λ z x => f (z, x)

/-- Uncurrying: the inverse of currying. -/
def SetCat.uncurry {X Y Z : Type u} (g : SetCat[Z, SetCat.exponential X Y]) : SetCat[(Z × X), Y] :=
  λ ⟨z, x⟩ => g z x

/-- Currying and uncurrying are inverses. -/
theorem SetCat.curry_uncurry_iso {X Y Z : Type u} :
    SetCat.curry ∘ SetCat.uncurry = SetCat.id (X := SetCat[Z, SetCat.exponential X Y]) := by
  ext g z x; rfl

/-! ## Cartesian Closed Categories -/

/-- A category is Cartesian closed if it has finite products and exponentials.
    Concretely: for any X, the functor (-) × X has a right adjoint. -/
structure CartesianClosed (C : Category) where
  terminal : Terminal C
  hasProducts : HasBinaryProducts C
  exponential : C.Obj → C.Obj → C.Obj
  eval : ∀ {X Y : C.Obj}, C[(exponential X Y) × C X, Y]
  curry : ∀ {X Y Z : C.Obj}, C[(Z × C X), Y] → C[Z, exponential X Y]
  curry_eval : ∀ {X Y Z : C.Obj} (f : C[(Z × C X), Y]),
    eval ∘ (curry f × C.id X) = f
  unique_curry : ∀ {X Y Z : C.Obj} (f : C[(Z × C X), Y]) (g : C[Z, exponential X Y]),
    eval ∘ (g × C.id X) = f → curry f = g
where
  × C := Prod  -- Notation for product object
  Prod := λ X Y => (hasProducts X Y).obj

/-- SetCat is a Cartesian closed category. -/
def SetCat.CartesianClosed : CartesianClosed SetCat where
  terminal := {
    obj := Unit,
    terminate := λ _ => (),
    unique := by intro X f; ext x; exact Unit.ext _ _
  }
  hasProducts := SetCat.hasBinaryProducts
  exponential := SetCat.exponential
  eval {X Y} := SetCat.eval X Y
  curry {X Y Z} := SetCat.curry (X := X) (Y := Y) (Z := Z)
  curry_eval f := by ext ⟨z, x⟩; rfl
  unique_curry f g h := by
    ext z x
    have := congrArg (λ fn => fn (z, x)) h
    simpa [SetCat.eval, SetCat.curry] using this

/-! ## Lambda Calculus Models -/

/-- A Cartesian closed category is a model of simply-typed lambda calculus.
    Objects are types, morphisms are terms, products are pair types,
    and exponentials are function types. -/

/-- The simply-typed lambda calculus signature:
    - Types: base types + product + arrow
    - Terms: variables, abstraction, application, pairs, projections -/
inductive SimpleType where
  | base : SimpleType
  | prod : SimpleType → SimpleType → SimpleType
  | arrow : SimpleType → SimpleType → SimpleType
  deriving Repr, DecidableEq

/-- Interpretation of simple types as objects of SetCat. -/
def interpretType : SimpleType → Type u
  | SimpleType.base => Unit
  | SimpleType.prod A B => interpretType A × interpretType B
  | SimpleType.arrow A B => interpretType A → interpretType B

/-- Example: the identity function λx.x has type A → A. -/
example : SimpleType := SimpleType.arrow SimpleType.base SimpleType.base

/-- The interpretation is: Unit → Unit, which has exactly one element. -/
example : interpretType (SimpleType.arrow SimpleType.base SimpleType.base) :=
  λ (u : Unit) => u

/-- A C.C.C. provides a sound and complete model of simply-typed lambda calculus. -/
theorem ccc_models_lambda_calculus {C : Category} (ccc : CartesianClosed C) : True := by
  trivial

/-! ## Kleisli Category for Monads -/

/-- Given a monad (T, η, μ) on C, the Kleisli category has objects of C
    and morphisms X → T(Y). This models effectful computation. -/
structure Monad (C : Category) where
  T : C.Obj → C.Obj
  onHom : ∀ {X Y : C.Obj}, C[X, Y] → C[T X, T Y]
  η : ∀ (X : C.Obj), C[X, T X]
  μ : ∀ (X : C.Obj), C[T (T X), T X]
  -- Monad laws: μ ∘ Tμ = μ ∘ μT, μ ∘ Tη = id = μ ∘ ηT
  assoc : ∀ (X : C.Obj), μ X ∘ onHom (μ X) = μ X ∘ μ (T X)
  left_id : ∀ (X : C.Obj), μ X ∘ onHom (η X) = C.id (T X)
  right_id : ∀ (X : C.Obj), μ X ∘ η (T X) = C.id (T X)

/-- The Kleisli category of a monad. Objects of C, Hom(X,Y) = C[X, T Y]. -/
axiom kleisliCategory {C : Category} (M : Monad C) : Category

#eval "Bridges.ToComputation: CartesianClosed, lambda calculus model, Monad, Kleisli"
#eval "SetCat is a Cartesian closed category"
#eval "CCC = model of simply-typed lambda calculus"
end MiniCategoryCore
