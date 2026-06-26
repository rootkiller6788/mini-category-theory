/-
# MiniMonadCore.Core.Basic

Monad on a category C: an endofunctor T : C → C with
unit η : 1_C ⇒ T and multiplication μ : T² ⇒ T satisfying the monad laws.

Also defined: comonad, strong monad, bimonad, Kleisli triple presentation.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad -/

structure Monad (C : Category) where
  T : Functor C C
  η : Functor.id C ⇒ T
  μ : Functor.comp T T ⇒ T
  leftUnit : ∀ (X : C.Obj),
    C.comp (μ.component X) (η.component (T.mapObj X)) = C.id (T.mapObj X)
  rightUnit : ∀ (X : C.Obj),
    C.comp (μ.component X) (T.mapHom (η.component X)) = C.id (T.mapObj X)
  associativity : ∀ (X : C.Obj),
    C.comp (μ.component X) (μ.component (T.mapObj X)) = C.comp (μ.component X) (T.mapHom (μ.component X))

/-! ## Monad Morphism -/

structure MonadMorphism {C : Category} (M N : Monad C) where
  component : M.T ⇒ N.T
  unitCompat : ∀ (X : C.Obj),
    C.comp (component.component X) (M.η.component X) = N.η.component X
  multCompat : ∀ (X : C.Obj),
    C.comp (component.component X) (M.μ.component X) =
    C.comp (N.μ.component X) (NaturalTransformation.vcomp (component) (component)).component X

/-! ## Comonad -/

structure Comonad (C : Category) where
  L : Functor C C
  ε : L ⇒ Functor.id C
  δ : L ⇒ Functor.comp L L
  leftCounit : ∀ (X : C.Obj),
    C.comp (ε.component (L.mapObj X)) (δ.component X) = C.id (L.mapObj X)
  rightCounit : ∀ (X : C.Obj),
    C.comp (L.mapHom (ε.component X)) (δ.component X) = C.id (L.mapObj X)
  coassociativity : ∀ (X : C.Obj),
    C.comp (δ.component (L.mapObj X)) (δ.component X) =
    C.comp (L.mapHom (δ.component X)) (δ.component X)

/-! ## Kleisli Triple (alternative monad presentation) -/

structure KleisliTriple (C : Category) where
  objMap : C.Obj → C.Obj
  unitMap : (X : C.Obj) → C[X, objMap X]
  extMap : (X Y : C.Obj) → C[X, objMap Y] → C[objMap X, objMap Y]
  extId : ∀ (X : C.Obj), extMap X X (unitMap X) = C.id (objMap X)
  extUnit : ∀ (X Y : C.Obj) (f : C[X, objMap Y]),
    C.comp (extMap X Y f) (unitMap X) = f
  extAssoc : ∀ (X Y Z : C.Obj) (f : C[X, objMap Y]) (g : C[Y, objMap Z]),
    C.comp (extMap Y Z g) (extMap X Y f) =
    extMap X Z (C.comp (extMap Y Z g) f)

/-! ## Strong Monad (for monoidal categories) -/

structure StrongMonad {C : Category} (M : Monad C) where
  strength : (X Y : C.Obj) → C[X, M.T.mapObj Y] → C[M.T.mapObj X, M.T.mapObj Y]
  strengthNaturality : ∀ (X Y Z W : C.Obj) (f : C[Z, X]) (g : C[Y, W]) (h : C[X, M.T.mapObj Y]),
    C.comp (M.T.mapHom g) (strength X Y h) = strength Z W (C.comp (M.T.mapHom g) (C.comp h f))
  unitStrength : ∀ (X Y : C.Obj) (x : C[X, Y]),
    C.comp (strength X Y (C.comp (M.η.component Y) x)) (M.η.component X) =
    C.comp (M.η.component (M.T.mapObj Y)) (M.T.mapHom x)

/-! ## Bimonad (monad + comonad compatible) -/

structure Bimonad (C : Category) where
  monad : Monad C
  comonad : Comonad C
  distribUnit : ∀ (X : C.Obj),
    C.comp (monad.η.component (comonad.L.mapObj X)) (comonad.ε.component X) = comonad.ε.component X
  distribMult : ∀ (X : C.Obj),
    C.comp (monad.μ.component (comonad.L.mapObj X)) (comonad.δ.component X) =
    C.comp (comonad.δ.component X) (comonad.L.mapHom (monad.η.component X))

/-! ## Pointed Endofunctor -/

structure PointedEndofunctor (C : Category) where
  T : Functor C C
  point : Functor.id C ⇒ T

def pointedToMonadCandidate {C : Category} (pe : PointedEndofunctor C)
    (μ : Functor.comp pe.T pe.T ⇒ pe.T)
    (hLeft : ∀ (X : C.Obj), C.comp (μ.component X) (pe.point.component (pe.T.mapObj X)) = C.id (pe.T.mapObj X))
    (hRight : ∀ (X : C.Obj), C.comp (μ.component X) (pe.T.mapHom (pe.point.component X)) = C.id (pe.T.mapObj X))
    (hAssoc : ∀ (X : C.Obj),
      C.comp (μ.component X) (μ.component (pe.T.mapObj X)) =
      C.comp (μ.component X) (pe.T.mapHom (μ.component X))) : Monad C := {
  T := pe.T
  η := pe.point
  μ := μ
  leftUnit := hLeft
  rightUnit := hRight
  associativity := hAssoc
}

/-! ## Identity Monad -/

def identityMonad (C : Category) : Monad C where
  T := Functor.id C
  η := NaturalTransformation.id (Functor.id C)
  μ := NaturalTransformation.id (Functor.id C)
  leftUnit X := by simp
  rightUnit X := by simp
  associativity X := by simp

/-! ## Monad on functor category [C, D] -/

structure FunctorCategoryMonad {C D : Category} where
  underlying : Functor C D
  T : Functor [C, D] [C, D]
  η : Functor.id [C, D] ⇒ T
  μ : Functor.comp T T ⇒ T
  leftUnit : ∀ (F : Functor C D) (X : C.Obj),
    D.comp (μ.component F (F.mapObj X)) (η.component (T.mapObj F) (F.mapObj X)) =
    D.id (T.mapObj F (F.mapObj X))
  rightUnit : ∀ (F : Functor C D) (X : C.Obj),
    D.comp (μ.component F (F.mapObj X))
      (T.mapHom (η.component F) (F.mapObj X)) =
    D.id (T.mapObj F (F.mapObj X))
  associativity : ∀ (F : Functor C D) (X : C.Obj),
    D.comp (μ.component F (F.mapObj X)) (μ.component (T.mapObj F) (F.mapObj X)) =
    D.comp (μ.component F (F.mapObj X)) (T.mapHom (μ.component F) (F.mapObj X))

#eval "Core.Basic: Monad (T, η, μ), MonadMorphism, Comonad, KleisliTriple"
#eval "Core.Basic: StrongMonad, Bimonad, PointedEndofunctor, identityMonad"
