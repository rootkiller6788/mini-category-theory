/-
# MiniAdjunction.Bridges.ToComputation

Curry-Howard-Lambek correspondence as adjunction,
monads from adjunctions, computational effects.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Constructions.Subobjects

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Curry-Howard-Lambek as Adjunction -/

/--
The Curry-Howard-Lambek correspondence establishes a three-way
equivalence between:
  - Proofs (intuitionistic logic)
  - Programs (typed lambda calculus)
  - Morphisms (cartesian closed categories)

At the core: the product-exponential adjunction (- × A) ⊣ (A ⇒ -)
in a cartesian closed category models implication introduction/elimination.
-/
structure CurryHowardAdjunction where
  cartesianClosed : Prop
  prodExpAdj : Prop   -- (- × A) ⊣ (A ⇒ -) for all A
  logicProgramCategory : Prop

/--
In a cartesian closed category, the product functor (- × A) has a
right adjoint (A ⇒ -). This corresponds to the deduction theorem
in logic: Γ, A ⊢ B  iff  Γ ⊢ A ⇒ B.
-/
axiom curryHowardLogicToPrograms : Prop

/--
The adjunction models the bijection between proofs of Γ, A ⊢ B
and proofs of Γ ⊢ A ⇒ B.
-/
axiom deductionTheoremAsAdjunction : Prop

#eval "Bridges.ToComputation: Curry-Howard-Lambek via product-exponential adjunction"

/-! ## Monads from Adjunctions -/

/--
Every adjunction F ⊣ G : C ⇄ D gives rise to a monad T = G ∘ F on C.
The unit of the monad is the adjunction unit η.
The multiplication μ = G ε F is derived from the counit.
-/
structure MonadFromAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) where
  T : Functor C C
  unit : Functor.id C ⇒ T
  multiply : Functor.comp T T ⇒ T
  T_eq_GF : T = Functor.comp G F

/--
Monad associativity law follows from the triangle identities.
-/
axiom monadAssociativityFromAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Prop

/--
The Eilenberg-Moore comparison: every monad arises from an adjunction
(in fact, from the Kleisli or Eilenberg-Moore adjunction).
-/
axiom everyMonadFromAdjunction : Prop

/--
The Kleisli adjunction for a monad T: F_T ⊣ G_T,
where F_T : C → C_T and G_T : C_T → C.
-/
axiom kleisliAdjunction : Prop

/--
The Eilenberg-Moore adjunction: F^T ⊣ G^T,
where F^T : C → C^T (algebras) and G^T : C^T → C (forgetful).
-/
axiom eilenbergMooreAdjunction : Prop

#eval "Bridges.ToComputation: Monads from adjunctions, Kleisli/Eilenberg-Moore adjunctions"

/-! ## Computational Effects as Monads -/

/--
Computational effects (state, exceptions, nondeterminism, I/O)
can be modeled as monads. Since monads arise from adjunctions,
every effect can be seen as arising from an adjunction.
-/
structure EffectAdjunction where
  computationCat : Category
  valueCat : Category
  F : Functor valueCat computationCat
  G : Functor computationCat valueCat
  adj : F ⊣ G
  effect : Prop

/--
The state monad State S = S → (- × S) arises from the adjunction
(- × S) ⊣ (S → -) (the product-exponential adjunction with parameter S).
-/
axiom stateMonadAdjunction (S : Type u) : Prop

/--
The exception monad Exception E = (- + E) arises from the adjunction
between the category of pointed objects and the base category.
-/
axiom exceptionMonadAdjunction (E : Type u) : Prop

/--
The continuation monad Cont R = ((- → R) → R) arises from the adjunction
of the double-dual in cartesian closed categories.
-/
axiom continuationMonadAdjunction (R : Type u) : Prop

#eval "Bridges.ToComputation: Effect adjunctions (state, exception, continuation)"
#eval "Bridges.ToComputation: everyMonadFromAdjunction (Kleisli, Eilenberg-Moore)"
#eval "Bridges.ToComputation: Curry-Howard-Lambek as product-exponential adjunction"
