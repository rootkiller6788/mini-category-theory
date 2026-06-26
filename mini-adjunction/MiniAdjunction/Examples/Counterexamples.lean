/-
# MiniAdjunction.Examples.Counterexamples

Non-adjoint functors, failure of adjoint conditions.
Examples: forgetful functor from fields, projections without products.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws
import MiniAdjunction.Properties.Preservation

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Non-Adjoint Functor: Forgetful from Fields -/

/--
The forgetful functor Field → Set does NOT have a left adjoint.
Reason: fields do not have free objects — the "free field" on a set
does not exist (you cannot freely invert elements in a general way).
-/
axiom forgetfulFieldNoLeftAdjoint : Prop

/--
The forgetful functor Field → Set does NOT have a right adjoint either.
Reason: the category of fields does not have products (the product
of two fields is not a field).
-/
axiom forgetfulFieldNoRightAdjoint : Prop

/-! ## Failure of Solution Set Condition -/

/--
A functor that does not satisfy the Solution Set Condition fails
to have a left adjoint (by Freyd's AFT).
Example: the inclusion of the category of fields into the category
of rings does not have a left adjoint.
-/
axiom noLeftAdjointCounterexample : Prop

/-! ## Projection Without Product -/

/--
The projection functor from a product category does not always
have a right adjoint unless the missing factor has a terminal object.
-/
axiom projectionNoRightAdjoint : Prop

/-! ## Constant Functor Without Limits -/

/--
A constant functor into a category without an initial object
does not have a left adjoint.
-/
axiom constantFunctorNoLeftAdjoint : Prop

/-! ## Non-Preservation of Limits -/

/--
A functor that does not preserve limits cannot be a right adjoint
(contrapositive of RAPL).
-/
axiom nonLimitPreservingNoRightAdjoint : Prop

/--
A functor that does not preserve colimits cannot be a left adjoint
(contrapositive of LAPC).
-/
axiom nonColimitPreservingNoLeftAdjoint : Prop

/-! ## Failure of Freyd's AFT -/

/--
Without the Solution Set Condition, a limit-preserving functor
may still fail to have a left adjoint.
Example: the inclusion of ordinal categories into Set.
-/
axiom freydAFTCounterexample : Prop

/-! ## Empty Category Issues -/

/--
A functor from the empty category always has a right adjoint
(the constant functor to the terminal object), but the left
adjoint only exists if the target has an initial object.
-/
axiom emptyCategoryAdjunctionIssues : Prop

/-! ## Discrete Category Counterexamples -/

/--
A functor between discrete categories 2 → 1 has no right adjoint
(where 2 = {0,1} discrete, 1 = {*} discrete).
It maps both objects to * and both identity maps to id_*.
-/
axiom discreteTwoToOneNoAdjunction : Prop

#eval "Examples.Counterexamples: forgetfulFieldNoLeftAdjoint, projectionNoRightAdjoint"
#eval "Examples.Counterexamples: nonLimitPreservingNoRightAdjoint (contrapositive RAPL)"
#eval "Examples.Counterexamples: Freyd AFT counterexample, discrete 2→1 no adjunction"
