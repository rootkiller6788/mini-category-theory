/-
# MiniMonadCore.Properties.ClassificationData

Classification data for monads: identity, constant, exception, state, reader monads.
Categorization of common computational monad types.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Monad Types (categorization) -/

inductive MonadType where
  | identity
  | constant
  | maybe
  | list
  | exception
  | state
  | reader
  | writer
  | cont
  deriving Repr, DecidableEq, BEq

def MonadType.describe : MonadType → String
  | .identity => "Identity monad: T(X) = X"
  | .constant => "Constant monad: T(X) = E"
  | .maybe => "Maybe/Option monad: T(X) = 1 + X"
  | .list => "List monad: T(X) = List X"
  | .exception => "Exception monad: T(X) = E + X"
  | .state => "State monad: T(X) = S → X × S"
  | .reader => "Reader monad: T(X) = E → X"
  | .writer => "Writer monad: T(X) = X × M"
  | .cont => "Continuation monad: T(X) = (X → R) → R"

/-! ## Identity Monad on SetCat -/

def idMonadSet : Monad SetCat where
  T := Functor.id SetCat
  η := {
    component := fun X x => x
    naturality := fun f => by
      funext x; rfl
  }
  μ := {
    component := fun X x => x
    naturality := fun f => by
      funext x; rfl
  }
  leftUnit X := rfl
  rightUnit X := rfl
  associativity X := rfl

/-! ## Constant Monad (at object E) on SetCat -/

def constantMonadSet (E : Type u) : Monad SetCat where
  T := Functor.const SetCat SetCat E
  η := {
    component := fun X _ => (C := SetCat).id E
    naturality := fun f => by
      simp [Functor.const, SetCat]
  }
  μ := {
    component := fun X e => e
    naturality := fun f => by
      simp [Functor.const, SetCat]
  }
  leftUnit X := by
    funext e; simp [SetCat, Functor.const]
  rightUnit X := by
    funext e; simp [SetCat, Functor.const]
  associativity X := by
    funext e; simp [SetCat, Functor.const]

/-! ## Maybe Monad on SetCat -/

def maybeMonadSet : Monad SetCat where
  T := {
    mapObj X := Option X
    mapHom f := Option.map f
    preservesId X := by
      funext x; cases x; rfl; rfl
    preservesComp g f := by
      funext x; cases x; rfl; rfl
  }
  η := {
    component := fun X x => some x
    naturality := fun f => by
      funext x; simp
  }
  μ := {
    component := fun X oo => Option.join oo
    naturality := fun f => by
      funext oo;
      cases oo; rfl;
      case some o => cases o; rfl; case some x => rfl
  }
  leftUnit X := by
    funext x; rfl
  rightUnit X := by
    funext o; cases o; rfl; rfl
  associativity X := by
    funext ooo; induction ooo <;> rfl

/-! ## #eval examples -/

#eval "Properties.ClassificationData: MonadType enumeration"
#eval "Properties.ClassificationData: idMonadSet on SetCat"
#eval "Properties.ClassificationData: maybeMonadSet (Option monad)"

end MiniMonadCore
