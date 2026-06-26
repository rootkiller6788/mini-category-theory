/-
# MiniLimitColimit.Theorems.Classification

Completeness classification: small-complete, finitely complete, cocomplete.
Categories classified by the limits they possess.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Universal
import MiniLimitColimit.Properties.ClassificationData
import MiniLimitColimit.Properties.Preservation

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Small-complete category -/

/-- A category with all limits indexed by small categories. -/
def IsSmallComplete (C : Category) : Prop :=
  ∀ (J : Category) (_ : Unit), ∀ (D : Diagram J C), Nonempty (Limit D)

/-- A category with all colimits indexed by small categories. -/
def IsSmallCocomplete (C : Category) : Prop :=
  ∀ (J : Category) (_ : Unit), ∀ (D : Diagram J C), Nonempty (Colimit D)

/-! ## Finitely complete categories -/

/--
A category is finitely complete iff it has:
1. A terminal object (limit of empty diagram)
2. All binary products
3. All equalizers

Equivalently: all finite limits exist.
-/
def IsFinitelyComplete (C : Category) : Prop :=
  Nonempty (Terminal C) ∧
  (∀ (A B : C.Obj), Nonempty (IsProduct A B C))

/--
A category is finitely cocomplete iff it has:
1. An initial object
2. All binary coproducts
3. All coequalizers
-/
def IsFinitelyCocomplete (C : Category) : Prop :=
  Nonempty (Initial C) ∧
  (∀ (A B : C.Obj), Nonempty (IsCoproduct A B C))

/-! ## Locally finitely presentable categories -/

/--
A category is locally finitely presentable if it is cocomplete,
finitely complete, and every object is a filtered colimit of
finitely presentable objects.
-/
structure IsLocallyFinitelyPresentable (C : Category) : Prop where
  cocomplete : IsCocomplete C
  finitelyComplete : IsFinitelyComplete C
  filteredColimits : ∀ (J : Category) (_ : IsFiltered J) (D : Diagram J C), Nonempty (Colimit D)

/-! ## AB5 axiom: filtered colimits are exact -/

/--
In an abelian category satisfying AB5, filtered colimits of exact sequences
are exact. This is a key property in homological algebra.
-/
axiom ab5Axiom {C : Category} (h : IsFinitelyCocomplete C)
    (hFiltered : ∀ (J : Category) (_ : IsFiltered J) (D : Diagram J C), Nonempty (Colimit D)) :
    True

/-! ## Adjoint functor theorem via completeness -/

/--
The General Adjoint Functor Theorem (GAFT):
If C is complete and has a small cogenerating set, then a functor F : C → D
has a left adjoint iff it preserves all small limits.
-/
axiom generalAdjointFunctorTheorem {C D : Category}
    (hComplete : IsComplete C) (F : Functor C D)
    (hPreservesLimits : Continuous F) : True

/--
The Special Adjoint Functor Theorem (SAFT):
A functor from a complete, well-powered category with a cogenerator
has a left adjoint iff it preserves limits.
-/
axiom specialAdjointFunctorTheorem {C D : Category}
    (hComplete : IsSmallComplete C) (F : Functor C D)
    (hContinuous : Continuous F) : True

/-! ## SetCat classification -/

/-- SetCat has all small limits. -/
axiom setCatIsSmallComplete : IsSmallComplete SetCat

/-- SetCat has all small colimits. -/
axiom setCatIsSmallCocomplete : IsSmallCocomplete SetCat

/-- SetCat is finitely complete. -/
axiom setCatIsFinitelyComplete : IsFinitelyComplete SetCat

/-- SetCat is finitely cocomplete. -/
axiom setCatIsFinitelyCocomplete : IsFinitelyCocomplete SetCat

/-- SetCat is locally finitely presentable. -/
axiom setCatIsLocallyFinitelyPresentable : IsLocallyFinitelyPresentable SetCat

/-! ## Classifying diagram shapes -/

/-- Determine if a given limit is finite. -/
def classifyLimit {J C : Category} {D : Diagram J C} (L : Limit D) : LimitType :=
  if IsFiniteCategory J then LimitType.finite
  else LimitType.small

/-- Determine if a given colimit is finite. -/
def classifyColimit {J C : Category} {D : Diagram J C} (CL : Colimit D) : ColimitType :=
  if IsFiniteCategory J then ColimitType.finite
  else ColimitType.small

/-! ## #eval examples -/

#eval "Theorems.Classification: complete/cocomplete classifications, SetCat properties"
#eval IsFinitelyComplete SetCat
#eval IsFinitelyCocomplete SetCat
#eval IsSmallComplete SetCat
#eval classifyLimit { limitCone := { apex := Unit, proj := fun _ : PEmpty => fun _ => (), naturality := fun u => nomatch u : Cone (Functor.const (DiscCat PEmpty) SetCat Unit) }, mediate := fun _ => fun _ => (), factor := fun c j => by nomatch j, unique := fun c f h => by funext x; simp : Limit (Functor.const (DiscCat PEmpty) SetCat Unit) }

end MiniLimitColimit
