/-
# MiniMonadCore.Constructions.Subobjects

Submonad: a sub-endofunctor closed under η and μ.
Monad ideal: a subfunctor of a monad closed under the monad operations.
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

/-! ## Submonad -/

structure Submonad {C : Category} (M : Monad C) where
  carrier : C.Obj → C.Obj
  inclusion : (X : C.Obj) → C[carrier X, M.T.mapObj X]
  closedUnderUnit : ∀ (X : C.Obj),
    ∃ (u : C[X, carrier X]), C.comp (inclusion X) u = M.η.component X
  closedUnderMult : ∀ (X : C.Obj),
    ∃ (m : C[carrier (carrier X), carrier X]),
      C.comp (inclusion X) m =
      C.comp (M.μ.component X) (C.comp (M.T.mapHom (inclusion X)) (inclusion (carrier X)))

/-! ## Quotient Monad -/

structure QuotientMonad {C : Category} (M N : Monad C) where
  projection : M.T ⇒ N.T
  surjective : ∀ (X : C.Obj),
    ∃ (s : C[N.T.mapObj X, M.T.mapObj X]),
      C.comp (projection.component X) s = C.id (N.T.mapObj X)
  preservesUnit : ∀ (X : C.Obj),
    C.comp (projection.component X) (M.η.component X) = N.η.component X
  preservesMult : ∀ (X : C.Obj),
    C.comp (projection.component X) (M.μ.component X) =
    C.comp (N.μ.component X)
      (NaturalTransformation.vcomp projection projection).component X

/-! ## Monad Ideal -/

structure MonadIdeal {C : Category} (M : Monad C) where
  idealObj : C.Obj → C.Obj
  embedding : (X : C.Obj) → C[idealObj X, M.T.mapObj X]
  absorbing : ∀ (X Y : C.Obj) (i : C[idealObj X, M.T.mapObj X])
    (f : C[X, M.T.mapObj Y]),
    C.comp (M.μ.component Y) (C.comp (M.T.mapHom f) (embedding X)) = embedding Y

/-! ## Trivial Submonad -/

def trivialSubmonad {C : Category} (M : Monad C) : Submonad M where
  carrier X := M.T.mapObj X
  inclusion X := C.id (M.T.mapObj X)
  closedUnderUnit X := ⟨M.η.component X, by simp [C.comp_id]⟩
  closedUnderMult X := ⟨M.μ.component X, by
    simp [C.comp_id, C.id_comp, M.T.preservesId]⟩

/-! ## Identity Submonad (unit image) -/

def unitSubmonad {C : Category} (M : Monad C) : Submonad M where
  carrier X := X
  inclusion X := M.η.component X
  closedUnderUnit X := ⟨C.id X, by simp [M.leftUnit]⟩
  closedUnderMult X := ⟨
    C.comp (M.η.component (M.T.mapObj X)) (M.η.component X),
    by
      simp [C.assoc, M.leftUnit, M.rightUnit, M.T.preservesComp]
  ⟩

/-! ## #eval examples -/

#eval "Constructions.Subobjects: Submonad structure"
#eval "Constructions.Subobjects: trivialSubmonad example"
#eval "Constructions.Subobjects: unitSubmonad (image of η)"

/-! ## Submonad Factorizations -/

theorem submonadFactorizes {C : Category} (M : Monad C) (S : Submonad M) (X : C.Obj) : Prop :=
  ∀ (f : C[X, S.carrier X]),
    C.comp (S.inclusion X) (C.id X) = C.comp (M.T.mapHom f) (C.id X)

structure SubmonadMorphism {C : Category} {M : Monad C} (S1 S2 : Submonad M) where
  component : (X : C.Obj) → C[S1.carrier X, S2.carrier X]
  naturality : ∀ (X Y : C.Obj) (f : C[X, Y]),
    C.comp (component Y) (S1.inclusion X) = C.comp (S2.inclusion X) (M.T.mapHom f)

def submonadInducesMonadMorphism {C : Category} {M : Monad C}
    (S : Submonad M) : Prop :=
  ∃ (N : Monad C) (φ : MonadMorphism N M),
    ∀ (X : C.Obj), φ.component.component X = S.inclusion X

/-! ## Submonad Lattice -/

theorem submonadInclusionPartialOrder {C : Category} {M : Monad C}
    (S1 S2 : Submonad M) : Prop :=
  (∀ (X : C.Obj), ∃ (f : C[S1.carrier X, S2.carrier X]),
    C.comp (S2.inclusion X) f = S1.inclusion X) ∨
  (∀ (X : C.Obj), ∃ (f : C[S2.carrier X, S1.carrier X]),
    C.comp (S1.inclusion X) f = S2.inclusion X)

#eval "Constructions.Subobjects: submonadFactorizes (factorization thm)"
#eval "Constructions.Subobjects: submonadInducesMonadMorphism"
#eval "Constructions.Subobjects: submonadInclusionPartialOrder"

/-! ## Intersection of Submonads -/

structure SubmonadIntersection {C : Category} (M : Monad C)
    (S1 S2 : Submonad M) where
  intersected : C.Obj → C.Obj
  isInclusion : ∀ (X : C.Obj), C[intersected X, M.T.mapObj X]
  factor1 : ∀ (X : C.Obj), ∃ (f : C[intersected X, S1.carrier X]),
    C.comp (S1.inclusion X) f = isInclusion X
  factor2 : ∀ (X : C.Obj), ∃ (f : C[intersected X, S2.carrier X]),
    C.comp (S2.inclusion X) f = isInclusion X

theorem submonadIntersectionIsSubmonad {C : Category} (M : Monad C)
    (S1 S2 : Submonad M) (SI : SubmonadIntersection M S1 S2) : Prop :=
  ∃ (S : Submonad M), ∀ (X : C.Obj), S.carrier X = SI.intersected X

/-! ## Union of Submonads -/

structure SubmonadUnion {C : Category} (M : Monad C) (S1 S2 : Submonad M) where
  united : C.Obj → C.Obj
  includes1 : ∀ (X : C.Obj), C[S1.carrier X, united X]
  includes2 : ∀ (X : C.Obj), C[S2.carrier X, united X]
  isUniversal : ∀ (X : C.Obj) (T : C.Obj) (i1 : C[S1.carrier X, T]) (i2 : C[S2.carrier X, T]),
    ∃! (f : C[united X, T]), C.comp f (includes1 X) = i1 ∧ C.comp f (includes2 X) = i2

#eval "Constructions.Subobjects: SubmonadIntersection with factor maps"
#eval "Constructions.Subobjects: submonadIntersectionIsSubmonad"
#eval "Constructions.Subobjects: SubmonadUnion universal property"

end MiniMonadCore
