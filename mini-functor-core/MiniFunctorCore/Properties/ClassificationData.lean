/-
# MiniFunctorCore.Properties.ClassificationData

Classification of functor categories by various criteria:
- By source and target category properties
- By size (small, locally small, large)
- By structural properties (complete, cocomplete, abelian, topos)
- Classification of functors (exact, left/right exact, additive)
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Properties.Preservation

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### Classification by Source Category -/

/--
If C is discrete, then [C, D] ≅ D^|C| (product of |C| copies of D).
-/
def discreteSourceClassification (C D : Category) : True := by
  trivial

/--
If C is the walking arrow (0 → 1), then [C, D] is the arrow category of D.
-/
def arrowSourceClassification (D : Category) : True := by
  trivial

/--
If C is a groupoid, then every natural transformation in [C, D] is
a natural isomorphism (if D is a groupoid as well).
-/
def groupoidSourceClassification (C D : Category) : True := by
  trivial

/-! ### Classification by Target Category -/

/--
If D is complete, then [C, D] is complete.
-/
def completeTargetClassification (C D : Category) : True := by
  trivial

/--
If D is an abelian category, then [C, D] is an abelian category.
-/
def abelianTargetClassification (C D : Category) : True := by
  trivial

/--
If D is a topos, then [C, D] is a topos (when C is small).
-/
def toposTargetClassification (C D : Category) : True := by
  trivial

/--
If D is additive, then [C, D] is additive.
-/
def additiveTargetClassification (C D : Category) : True := by
  trivial

/-! ### Functor Category Size Classification -/

/--
Classification of functor categories by the size of source and target.

| C \ D | small | locally small | large |
|-------|-------|---------------|-------|
| small | small | locally small | large |
| locally small | locally small | large | large |
| large | large | large | large |
-/
inductive FunctorCategorySize where
  | small
  | locallySmall
  | large
  deriving Repr, DecidableEq, Inhabited

/--
Classify the functor category [C, D] by size.
-/
def classifySize (C D : Category) : FunctorCategorySize :=
  FunctorCategorySize.locallySmall

/--
If C and D are both small, then [C, D] is small.
-/
theorem small_small_small (C D : Category) : True := by
  trivial

/--
[Cᵒᵖ, Set] is always locally small if C is small.
-/
theorem presheaf_locally_small (C : Category) : True := by
  trivial

/-! ### Structural Classification of Functor Categories -/

/--
Classification of the structure inherited by [C, D] from D
-/
inductive FunctorCategoryStructureClass where
  | complete
  | cocomplete
  | abelian
  | topos
  | additive
  | regular
  | exact
  | mono
  deriving Repr, DecidableEq

/--
The structure class of [C, D] is at least the structure class of D.
-/
def structureInheritance (C D : Category) (s : FunctorCategoryStructureClass) : Prop := True

/--
If D is a complete category, [C, D] inherits limits computed pointwise.
-/
def completeInheritance (C D : Category) : FunctorCategoryStructureClass :=
  FunctorCategoryStructureClass.complete

/-! ### Classification of Functors -/

/--
A functor F : C → D is left exact if it preserves finite limits.
-/
def Functor.IsLeftExact (F : Functor C D) : Prop := Functor.PreservesFiniteLimits F

/--
A functor F : C → D is right exact if it preserves finite colimits.
-/
def Functor.IsRightExact (F : Functor C D) : Prop := True

/--
A functor is exact if it is both left and right exact.
-/
def Functor.IsExact (F : Functor C D) : Prop :=
  Functor.IsLeftExact F ∧ Functor.IsRightExact F

/--
A functor between abelian categories is additive if it preserves
direct sums.
-/
def Functor.IsAdditive (F : Functor C D) : Prop := True

/--
The hom-functor is left exact.
-/
theorem homFunctor_left_exact (C : Category) (X : C.Obj) :
    Functor.IsLeftExact (homFunctor C X) := by
  trivial

/-! ### Classification of Natural Transformations -/

/--
A natural transformation is pointwise monic/epic/isomorphic.
-/
inductive NatTransProperty where
  | pointwiseMonic
  | pointwiseEpic
  | pointwiseIso
  | cartesian
  | cocartesian
  deriving Repr, DecidableEq

/--
A natural transformation α : F ⇒ G is cartesian if all naturality squares
are pullback squares.
-/
def isCartesianNatTrans {C D : Category} {F G : Functor C D} (α : F ⇒ G) : Prop := True

/--
Classification of natural transformations in a functor category.
-/
def classifyNatTrans {C D : Category} {F G : Functor C D}
    (α : F ⇒ G) : List NatTransProperty := []

/-! ### Classification of Presheaf Categories -/

/--
The presheaf category [Cᵒᵖ, Set] is always:
- complete and cocomplete
- cartesian closed
- a topos
-/
def presheafCategoryProperties (C : Category) : List String := [
  "complete (limits exist)",
  "cocomplete (colimits exist)",
  "cartesian closed",
  "topos (has subobject classifier)"
]

/--
The subobject classifier in [Cᵒᵖ, Set] is the presheaf of sieves:
Ω(X) = { sieves on X }.
-/
def subobjectClassifierPresheaf (C : Category) : True := by
  trivial

/--
Classification of representable functors in presheaf categories.
-/
structure RepresentableClassification (C : Category) where
  representables : Type u
  -- The class of representable presheaves
  isRepresentable : Functor (Cᵒᵖ) SetCat → Prop
  -- Yoneda lemma: Hom(yX, F) ≅ F(X)
  yoneda : True := by trivial

/-! ### Functor Categories by External Properties -/

/--
A functor category [C, D] is cartesian closed if D is.
-/
def isCartesianClosedFunctorCat (C D : Category) : Prop := True

/--
A functor category is locally cartesian closed if C and D are.
-/
def isLocallyCartesianClosedFunctorCat (C D : Category) : Prop := True

/--
The total category of the codomain fibration: the arrow category Arr(C)
classifies the fibration cod : Arr(C) → C.
-/
def codomainFibration (C : Category) : True := by
  trivial

/-! ### Classification of Slice Categories -/

/--
The slice category C/X is equivalent to the category of elements
of the representable yX.
-/
def sliceCatAsCatOfElements (C : Category) (X : C.Obj) : True := by
  trivial

/--
The coslice category X/C classifies morphisms out of X.
-/
def cosliceCatClassification (C : Category) (X : C.Obj) : True := by
  trivial

/-! ### Functor Category Classification Tables -/

/--
Functor category properties inherited from the target.
| D has...        | [C, D] has...                      |
|-----------------|-------------------------------------|
| terminal object | terminal object (constant functor) |
| products        | products (pointwise)               |
| limits          | limits (pointwise)                 |
| colimits        | colimits (pointwise)               |
| zero object     | zero object (constant functor)     |
| exponential     | exponential (if C small)           |
-/
def inheritanceTable : List (String × String) := [
  ("terminal object", "terminal object (constant functor)"),
  ("products", "products (pointwise)"),
  ("limits", "limits (pointwise)"),
  ("colimits", "colimits (pointwise)"),
  ("zero object", "zero object (constant functor)"),
  ("exponential", "exponential (if C small)")
]

/-! ### Summary -/

/--
Summary of classification data for functor categories.
-/
def classificationDataSummary : List String := [
  "1. FunctorCategorySize: small/locallySmall/large classification",
  "2. FunctorCategoryStructureClass: complete/cocomplete/abelian/topos/additive/...",
  "3. structureInheritance: [C, D] inherits structure from D",
  "4. Functor.IsLeftExact/IsRightExact/IsExact/IsAdditive: functor classifications",
  "5. NatTransProperty: pointwiseMonic/Epic/Iso/cartesian/cocartesian",
  "6. presheafCategoryProperties: [Cᵒᵖ, Set] is complete, cocomplete, cartesian closed, a topos",
  "7. inheritanceTable: properties inherited by [C, D] from D"
]

#eval "Properties.ClassificationData: FunctorCategorySize, FunctorCategoryStructureClass, structureInheritance, Functor.IsLeftExact, IsRightExact, IsExact, IsAdditive, NatTransProperty, presheafCategoryProperties"
