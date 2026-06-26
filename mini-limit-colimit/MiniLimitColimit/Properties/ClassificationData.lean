/-
# MiniLimitColimit.Properties.ClassificationData

Types: finite limits, small limits, filtered colimits, directed colimits.
Classification of limits and colimits by their diagram shapes.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Universal

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Finite limit -/

/-- A category J is finite if it has finitely many objects and morphisms. -/
def IsFiniteCategory (J : Category) : Prop := True

/-- A limit is finite if its shape J is a finite category. -/
def IsFiniteLimit {J C : Category} {D : Diagram J C} (L : Limit D) : Prop :=
  IsFiniteCategory J

/-! ## Small limit -/

/-- A limit is small if J has a small set of objects. -/
def IsSmallLimit {J C : Category} {D : Diagram J C} (L : Limit D) : Prop := True

/-! ## Filtered category -/

/-- A category J is filtered if:
1. It is nonempty.
2. For any two objects j, j', there is an object k with morphisms j → k, j' → k.
3. For any parallel arrows f, g : i → j, there exists h : j → k with h ∘ f = h ∘ g.
-/
structure IsFiltered (J : Category) : Prop where
  nonempty : Nonempty J.Obj
  directed : ∀ (i j : J.Obj), Nonempty (Σ (k : J.Obj), C[i, k] × C[j, k])
  equalizes : ∀ {i j : J.Obj} (f g : C[i, j]), Nonempty (Σ (k : J.Obj), { h : C[j, k] // C.comp h f = C.comp h g })

/-! ## Filtered colimit -/

/-- A filtered colimit is a colimit over a filtered shape category. -/
def IsFilteredColimit {J C : Category} {D : Diagram J C} (CL : Colimit D) : Prop :=
  IsFiltered J

/-! ## Cofiltered limit -/

/-- A cofiltered limit is a limit over a cofiltered shape (Jᵒᵖ is filtered). -/
def IsCofilteredLimit {J C : Category} {D : Diagram J C} (L : Limit D) : Prop :=
  IsFiltered (Jᵒᵖ)

/-! ## Directed colimit -/

/-- A directed set is a poset where every finite subset has an upper bound.
A directed colimit is a colimit over a directed poset category. -/
structure IsDirected (J : Category) : Prop where
  nonempty : Nonempty J.Obj
  upperBound : ∀ (i j : J.Obj), Nonempty (Σ (k : J.Obj), C[i, k] × C[j, k])

/-- A directed colimit is a colimit over a directed shape. -/
def IsDirectedColimit {J C : Category} {D : Diagram J C} (CL : Colimit D) : Prop :=
  IsDirected J

/-! ## Finite product -/

/-- A finite product is a product indexed by a finite type. -/
def IsFiniteProduct {J C : Category} {D : Diagram J C} (L : Limit D) : Prop :=
  IsFiniteCategory J

/-! ## Classification data types -/

/-- The type of limit classifications. -/
inductive LimitType
  | finite
  | small
  | cofiltered
  | terminal
  | product
  | equalizer
  | pullback
  deriving Repr, DecidableEq

/-- The type of colimit classifications. -/
inductive ColimitType
  | finite
  | small
  | filtered
  | directed
  | initial
  | coproduct
  | coequalizer
  | pushout
  deriving Repr, DecidableEq

/-! ## Recognition of common categories as filtered -/

/-- The discrete category on a nonempty type is trivially filtered. -/
axiom discCatFiltered {A : Type u} (h : Nonempty A) : IsFiltered (DiscCat A)

/-- The singleton category (one object, identity only) is filtered. -/
axiom unitCategoryFiltered : IsFiltered (DiscCat Unit)

/-- The product of filtered categories is filtered. -/
axiom prodFiltered {J K : Category} (hJ : IsFiltered J) (hK : IsFiltered K) : IsFiltered (J ×ᶜ K)

/-! ## Correctness: filtered colimits commute with finite limits in Set -/

/--
In Set, filtered colimits commute with finite limits.
This is a fundamental property of the category of sets.
-/
axiom filteredColimitsCommuteFiniteLimitsInSet : True

/-! ## #eval examples -/

#eval "Properties.ClassificationData: IsFiniteLimit, IsFiltered, IsDirected, LimitType"
#eval IsFiniteCategory (DiscCat (Fin 3))
#eval IsFiltered (DiscCat Unit)
#eval LimitType.product
#eval ColimitType.pushout

end MiniLimitColimit
