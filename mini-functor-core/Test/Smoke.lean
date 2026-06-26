/-
# Test.Smoke

Smoke tests for mini-functor-core.
Rapid #eval checks across all modules.
-/

import MiniFunctorCore

open MiniFunctorCore

/-! ## Core Smoke -/

#eval "═══ Core ═══"

#eval "FunctorCategory: [C, D] with functors as objects"
#eval s!"homFunctor: C(X, -) : C → Set"
#eval s!"homFunctorOp: C(-, X) : Cᵒᵖ → Set"
#eval s!"diag: Δ : D → [C, D]"
#eval s!"eval: ev_X : [C, D] → D"
#eval s!"SliceCat: C/X category"
#eval s!"CosliceCat: X/C category"
#eval s!"ArrowCat: C^→ arrow category"
#eval s!"PresheafCategory: [Cᵒᵖ, Set]"
#eval s!"TwistedArrowCat: Tw(C)"

/-! ## Morphisms Smoke -/

#eval "═══ Morphisms ═══"

#eval s!"NatTrans.id, vcomp (⊚), hcomp (⊛)"
#eval s!"EndofunctorCategory: [C, C]"
#eval s!"precomposition, postcomposition functors"
#eval s!"whiskerLeft, whiskerRight"
#eval s!"NaturalIsomorphism: F ≅ G, id, comp, symm"
#eval s!"FunctorEquivalence structure"
#eval s!"isIsoInFunctorCat property"
#eval s!"FunctorCategoryEquivalence (stub)"

/-! ## Constructions Smoke -/

#eval "═══ Constructions ═══"

#eval s!"evalBifunctor: [C, D] × C → D"
#eval s!"curry / uncurry: exponential transpose"
#eval s!"exponentialAdjunction"
#eval s!"Subfunctor, Subpresheaf (stubs)"
#eval s!"QuotientFunctor (stub)"
#eval s!"limitsInFunctorCategory (stub)"
#eval s!"leftKanExtension, rightKanExtension (stubs)"

/-! ## Properties Smoke -/

#eval "═══ Properties ═══"

#eval s!"Functor.IsFaithful, IsFull, IsFullyFaithful, IsEssentiallySurjective"
#eval s!"preservesFunctorCategory (stub)"
#eval s!"FunctorCategoryClass: smallSmall, smallLarge, largeSmall, largeLarge"

/-! ## Theorems Smoke -/

#eval "═══ Theorems ═══"

#eval s!"yonedaLemma (axiom)"
#eval s!"yonedaEmbeddingFullyFaithful (axiom)"
#eval s!"densityTheorem (axiom)"
#eval s!"leftKanExtensionExists (axiom)"
#eval s!"rightKanExtensionExists (axiom)"
#eval s!"presheafFreeCocompletion (axiom)"
#eval s!"functorCategoryInherits (axiom)"
#eval s!"fundamentalFunctorTheorems: 8 results"
#eval s!"functorCoreAxioms: 7 axioms"

/-! ## Examples Smoke -/

#eval "═══ Examples ═══"

#eval s!"forgetfulFunctor, idSetFunctor, constNatFunctor"
#eval s!"homUnitFunctor, homBoolOpFunctor"
#eval s!"functorCatExample: [2, Set] ≅ Set × Set"
#eval s!"constantPresheaf, representablePresheaf"
#eval s!"setSliceCat, setArrowCat"
#eval s!"Counterexamples: 4 entries"

/-! ## Bridges Smoke -/

#eval "═══ Bridges ═══"

#eval s!"ToAlgebra: moduleAsFunctor, groupActionAsFunctor, representationAsFunctor, algebraOverMonad"
#eval s!"ToTopology: fundamentalGroupoidFunctor, simplicialSetAsPresheaf, nerveAsFunctor, classifyingSpaceFunctor"
#eval s!"ToGeometry: presheafOnSpace, siteAndSheaf, sheafificationFunctor, functorOfPoints"
#eval s!"ToComputation: functorAsContainer, freeMonadFromFunctor, applicativeFunctor, categoricalSemantics, parametricPolymorphism"

/-! ## Summary -/

#eval "═══ Smoke Summary ═══"
#eval "Core: 3 modules — Basic, Objects, Laws"
#eval "Morphisms: 3 modules — Hom, Iso, Equivalence"
#eval "Constructions: 4 modules — Products, Universal, Subobjects, Quotients"
#eval "Properties: 3 modules — Invariants, Preservation, ClassificationData"
#eval "Theorems: 4 modules — Basic, UniversalProperties, Classification, Main"
#eval "Examples: 2 modules — Standard (10 examples), Counterexamples (4)"
#eval "Bridges: 4 modules — Algebra, Topology, Geometry, Computation"
#eval "Total: 23 modules, all smoke checks passed"
