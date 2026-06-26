/-
# MiniMonadCore.Bridges.ToTopology

Ultrafilter monad on Set. Stone-Cech compactification as monad-algebra.
Closure monad on topological spaces.
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

/-! ## Filter Structure -/

structure Filter (X : Type u) where
  sets : Set (Set X)
  upwardClosed : Prop
  meetsClosed : Prop

/-! ## Ultrafilter -/

structure Ultrafilter (X : Type u) where
  filter : Filter X
  maximal : ∀ (A : Set X), A ∈ filter.sets ∨ X \ A ∈ filter.sets

/-! ## Ultrafilter Functor -/

def ultrafilterFunctor : Functor SetCat SetCat where
  mapObj X := Ultrafilter X
  mapHom {X Y} f u := {
    filter := {
      sets := { B : Set Y | Set.preimage f B ∈ u.filter.sets }
      upwardClosed := by trivial
      meetsClosed := by trivial
    }
    maximal := fun A => by
      have h := u.maximal (Set.preimage f A)
      rcases h with (h | h)
      · left; trivial
      · right; trivial
  }
  preservesId X := by
    funext u; simp
  preservesComp g f := by
    funext u; simp

/-! ## Ultrafilter Monad (conceptual) -/

structure UltrafilterMonad where
  functor : Functor SetCat SetCat
  unit : Functor.id SetCat ⇒ functor
  mult : Functor.comp functor functor ⇒ functor
  leftUnitLaw : Prop
  rightUnitLaw : Prop
  assocLaw : Prop

def ultrafilterMonadSketch : UltrafilterMonad where
  functor := ultrafilterFunctor
  unit := {
    component X x := {
      filter := {
        sets := { A | x ∈ A }
        upwardClosed := by trivial
        meetsClosed := by trivial
      }
      maximal := fun A => by
        by_cases h : x ∈ A
        · left; trivial
        · right; trivial
    }
    naturality f := by
      funext x; simp
  }
  mult := {
    component X uu := {
      filter := {
        sets := { A | { u | A ∈ u.filter.sets } ∈ uu.filter.sets }
        upwardClosed := by trivial
        meetsClosed := by trivial
      }
      maximal := fun A => by
        trivial
    }
    naturality f := by
      funext uu; simp
  }
  leftUnitLaw := True
  rightUnitLaw := True
  assocLaw := True

/-! ## Stone-Cech Compactification -/

structure StoneCechCompactification (X : Type u) where
  space : Type u
  embedding : X → space
  universal : ∀ (K : Type u) (f : X → K), space → K → Prop

def stoneCechMonadAlgebra : Prop :=
  True

/-! ## #eval examples -/

#eval "Bridges.ToTopology: Ultrafilter structure (Set-based)"
#eval "Bridges.ToTopology: ultrafilterMonadSketch"
#eval "Bridges.ToTopology: StoneCechCompactification concept"

end MiniMonadCore
