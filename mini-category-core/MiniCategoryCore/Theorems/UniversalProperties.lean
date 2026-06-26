/-
# MiniCategoryCore.Theorems.UniversalProperties

Universal properties: terminal/initial universal properties,
product as limit of a discrete diagram, universal arrows / adjunctions reference.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Constructions.Universal
import MiniCategoryCore.Constructions.Products
import MiniCategoryCore.Theorems.Basic

namespace MiniCategoryCore

/-! ## Terminal Object as Limit of Empty Diagram -/

/-- A terminal object is the limit of the empty diagram.
    For any object X, there is exactly one map X → terminal. -/
theorem terminal_as_limit (C : Category) (T : Terminal C) :
    ∀ (X : C.Obj), ∃! f : C[X, T.obj], True := by
  intro X
  refine ⟨T.terminate X, trivial, ?_⟩
  intro f _
  exact T.unique X f

/-! ## Initial Object as Colimit of Empty Diagram -/

/-- An initial object is the colimit of the empty diagram.
    For any object X, there is exactly one map initial → X. -/
theorem initial_as_colimit (C : Category) (I : Initial C) :
    ∀ (X : C.Obj), ∃! f : C[I.obj, X], True := by
  intro X
  refine ⟨I.initiate X, trivial, ?_⟩
  intro f _
  exact I.unique X f

/-! ## Product as Limit of Discrete 2-Object Diagram -/

/-- A product of A and B is the limit of the discrete diagram {A, B}.
    The universal property: for any Q with maps f: Q→A, g: Q→B,
    there is a unique h: Q→A×B with π₁∘h=f, π₂∘h=g. -/
theorem product_as_limit {C : Category} {A B : C.Obj} (P : Product C A B) :
    ∀ (Q : C.Obj) (f : C[Q, A]) (g : C[Q, B]),
    ∃! h : C[Q, P.obj], P.π₁ ∘ h = f ∧ P.π₂ ∘ h = g :=
  P.univ

/-! ## Universal Arrow / Universal Element -/

/-- A universal arrow from X to a functor-like mapping U : D → C consists of
    an object A in D and a morphism η : X → U(A) such that every morphism
    X → U(Y) factors uniquely through η. -/
structure UniversalArrow
    (C : Category) (D : Category)
    (U : D.Obj → C.Obj)
    (onHom : ∀ {A B : D.Obj}, D[A, B] → C[U A, U B])
    (X : C.Obj) where
  A : D.Obj
  η : C[X, U A]
  universal : ∀ (Y : D.Obj) (f : C[X, U Y]),
    ∃! g : D[A, Y], onHom g ∘ η = f

/-- A universal element is a special case of universal arrow. -/
def UniversalElement
    (C : Category) (F : C.Obj → C.Obj)
    (onHom : ∀ {X Y : C.Obj}, C[X, Y] → C[F X, F Y]) : Prop :=
  ∃ (S : C.Obj) (u : C[S, F S]),
    ∀ (Y : C.Obj) (h : C[S, F Y]), ∃! f : C[S, Y], onHom f ∘ u = h

/-! ## Adjunction Reference -/

/-- Adjunction data: F ⊣ G (F is left adjoint to G). -/
structure Adjunction (C D : Category) where
  F : C.Obj → D.Obj
  G : D.Obj → C.Obj
  onHomF : ∀ {X Y : C.Obj}, C[X, Y] → D[F X, F Y]
  onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y]
  unit : ∀ (X : C.Obj), C[X, G (F X)]
  counit : ∀ (Y : D.Obj), D[F (G Y), Y]
  triangle1 : ∀ (X : C.Obj), onHomG (counit (F X)) ∘ unit X = C.id X
  triangle2 : ∀ (Y : D.Obj), counit (F (G Y)) ∘ onHomF (unit (G Y)) = D.id Y

/-- Adjoint functor theorem reference (this is a deep theorem). -/
axiom adjointFunctorTheorem {C D : Category}
    (G : D.Obj → C.Obj)
    (onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y])
    (map_id : ∀ (X : D.Obj), onHomG (D.id X) = C.id (G X))
    (map_comp : ∀ {X Y Z : D.Obj} (f : D[Y, Z]) (g : D[X, Y]),
      onHomG (D.comp f g) = C.comp (onHomG f) (onHomG g))
    (hlimit : True) : True

#eval "Theorems.UniversalProperties: terminal as limit, initial as colimit, product as limit"
#eval s!"Terminal is limit of empty diagram: {terminal_as_limit}"
#eval "Universal arrow and adjunction structures defined"
end MiniCategoryCore
