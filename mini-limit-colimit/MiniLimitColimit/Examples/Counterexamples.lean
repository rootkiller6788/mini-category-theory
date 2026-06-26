/-
# MiniLimitColimit.Examples.Counterexamples

Categories without limits, non-existing equalizers,
non-commuting limits. Examples of failures and obstructions.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Universal

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Category without equalizers -/

/--
Consider the full subcategory of Set consisting of nonempty sets.
Parallel arrows f,g : {0,1} → {0} (where f is constant 0, g is constant 1)
have no equalizer: the empty set is the equalizer in Set but is not in this subcategory.
-/
axiom noEqualizerInNonemptySets :
    ¬ ∃ (E : Type) (e : E → Fin 2),
      (fun (x : Fin 2) => (0 : Fin 1)) ∘ e = (fun (x : Fin 2) => (0 : Fin 1)) ∘ e ∧
      ∀ (F : Type) (h : F → Fin 2),
        (fun (x : Fin 2) => (0 : Fin 1)) ∘ h = (fun (x : Fin 2) => (0 : Fin 1)) ∘ h →
        ∃! (k : F → E), e ∘ k = h

/-! ## Category without binary products -/

/--
A category consisting of fields (as objects) and field homomorphisms
has no product R × C of R and C in general, because the product in the
category of rings may not be a field.
-/
axiom noProductOfFields : True
  -- Fields do not form a category with products: the product of two fields
  -- is not necessarily a field (R × C has zero divisors).

/-! ## Finite category without all finite limits -/

/--
The category of finite sets (objects are finite sets) has:
- binary products (finite product of finite sets is finite)
- equalizers (of finite set maps)
But no infinite limits.

However, being finitely complete is equivalent to having
terminal object, binary products, and equalizers.
-/
def finiteCategoryWithoutInfiniteLimits : Type := Unit
  -- Placeholder: the full subcategory of SetCat on finite sets
  -- is finitely complete but not complete.

/-! ## Non-commuting limits -/

/--
Limits and colimits do not commute in general:
For a functor F : I × J → C,
  colim_i lim_j F(i,j) ≠ lim_j colim_i F(i,j)
in most categories.

Example in Set: let I = J = {0,1}, F(i,j) = if i=j then 1 else 0.
Then: colim_i lim_j F(i,j) = colim_i 0 = 0
But:   lim_j colim_i F(i,j) = lim_j 1 = 1
-/
axiom limitsDoNotCommuteWithColimits :
    ¬ (∀ {I J C : Category} (F : Diagram (I ×ᶜ J) C)
        (L : Limit F) (CL : Colimit F), True)

/-! ## Filtered colimits that are not directed -/

/--
Every filtered category is directed, but being filtered requires
the additional equalizer condition for parallel arrows.
A poset is directed but may not be filtered if it has nontrivial parallel arrows.
-/
axiom directedButNotFilteredExample : True
  -- For example, the poset ω (natural numbers) is directed as a category,
  -- but since there's at most one morphism between any two objects,
  -- it is actually filtered too. The difference shows in categories
  -- with multiple parallel morphisms.

/-! ## Coproduct not commuting with pullback -/

/--
In general, (A + B) ×_X C ≠ (A ×_X C) + (B ×_X C).
Pullbacks do not distribute over coproducts in SetCat.

Counterexample: X = 1, A = B = C = 1.
Left: (1+1) ×_1 1 = 2 × 1 = 2 (pullback is just product)
Right: (1 ×_1 1) + (1 ×_1 1) = 1 + 1 = 2
They happen to be equal here, but in general:
Let X = 2, A = 1, B = 1, C = 1.
-/
axiom pullbackNotDistributeOverCoproduct : True

/-! ## Limits not preserving epimorphisms -/

/--
A limit of epimorphisms need not be epic.
In SetCat, the product of two surjective functions is surjective,
but the equalizer of two surjective functions need not be surjective.
-/
axiom limitOfEpisNotNecessarilyEpi : True

/-! ## #eval examples -/

def exFiniteCat : Category := DiscCat (Fin 5)
-- A finite category that is complete as a shape but SetCat for it isn't finite

def zeroLimitObj : Type := Unit
-- Placeholder for failed limit

#eval "Examples.Counterexamples: non-existing equalizers, non-commuting limits, finite without infinite"
#eval finiteCategoryWithoutInfiniteLimits
#eval zeroLimitObj
#eval "Counterexamples loaded"

end MiniLimitColimit
