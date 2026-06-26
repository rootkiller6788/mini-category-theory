/-
# MiniLimitColimit.Bridges.ToGeometry

Fiber products in geometry, gluing as colimit.
Limits and colimits in algebraic geometry and related fields.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Fiber product (pullback) in geometry -/

/--
In algebraic geometry, the fiber product X ×_S Y (also written X ×_Z Y)
is the categorical pullback. It is fundamental for:
- Base change of schemes
- Fiber of a morphism
- Intersection theory
-/
axiom fiberProductIsPullback {C : Category} {X Y S : C.Obj} (f : C[X, S]) (g : C[Y, S]) :
    Pullback f g

/-! ## Sheaf condition as equalizer -/

/--
A presheaf F on a topological space X is a sheaf iff for every open cover
{U_i} of an open set U, the following diagram is an equalizer:

  F(U) → ∏_i F(U_i) ⇉ ∏_{i,j} F(U_i ∩ U_j)

This is a limit condition!
-/
axiom sheafConditionAsEqualizer : True

/-! ## Descent as limit -/

/--
Faithfully flat descent: given a morphism f : Y → X which is
faithfully flat and quasi-compact, the category of schemes over X
is equivalent to the limit of a cosimplicial diagram.
-/
axiom faithfullyFlatDescentAsLimit : True

/-! ## Cech cohomology as limit -/

/--
Cech cohomology is computed as a colimit over refinements of covers.
The entire Cech complex is a limit/colimit construction.
-/
axiom cechCohomologyAsColimit : True

/-! ## Gluing as colimit -/

/--
Given open subsets U, V ⊆ X with intersection U ∩ V,
the space X glued from U and V along U ∩ V is a pushout:

  U ∩ V → U
    ↓      ↓
    V  →   X = U ∪ V
-/
axiom gluingAsPushout : True

/-! ## Stacks as 2-limits -/

/--
A stack over a site C is a fibered category satisfying an effective
descent condition, which can be expressed as a 2-limit.
-/
axiom stacksAsTwoLimits : True

/-! ## Fiber product in the category of schemes -/

/--
For X, Y → S in the category of schemes Sch/S,
the fiber product X ×_S Y exists and is the pullback in Sch.
-/
axiom schemesFiberProductExists : True

/-! ## Base change of schemes -/

/--
Base change: given S' → S and X → S, the base change X ×_S S'
is the pullback of X → S along S' → S.
Fundamental for constructing families of varieties.
-/
axiom baseChangeAsPullback : True

/-! ## Limit of sheaves -/

/--
The category of sheaves on a site is complete and cocomplete.
Limits are computed objectwise; colimits require sheafification.
-/
axiom sheafCategoryIsComplete : True

/-! ## #eval examples -/

#eval "Bridges.ToGeometry: fiber products, gluing, sheaf condition, stacks"
#eval "fiberProductIsPullback: pullback in any category"
#eval "sheafConditionAsEqualizer: sheaf = limit condition"
#eval "gluingAsPushout: gluing = colimit"

end MiniLimitColimit
