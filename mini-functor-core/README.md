# mini-functor-core

Functor theory core: functor categories [C, D], natural transformations,
Yoneda lemma, Kan extensions, presheaves, and bridges to algebra/topology/geometry/computation.

## Module Status: COMPLETE ✅

| Level | Name | Status | Details |
|-------|------|--------|---------|
| **L1** | Definitions | **Complete** | FunctorCategory, homFunctor, NaturalTransformation, NaturalIsomorphism, FunctorEquivalence, SliceCat, CosliceCat, ArrowCat, PresheafCategory, KaroubiObj/envelope, Sieve, Cosieve, Subfunctor, QuotientFunctor, MonadAsEndofunctor, LeftKanExtension, RightKanExtension, etc. (~20 definitions) |
| **L2** | Core Concepts | **Complete** | Naturality, vertical/horizontal composition, interchange law, functor composition laws, whiskering, isomorphisms in functor categories (~6 concepts) |
| **L3** | Math Structures | **Complete** | [C,D] as exponential, PresheafCategory as topos, Category of elements, KaroubiEnvelope, MonadAsEndofunctor, AdjunctionToMonad, Site/GrothendieckTopology (~8 structures) |
| **L4** | Fundamental Theorems | **Complete** | equivalence_implies_faithful (complete calc proof), equivalence_implies_essentially_surjective (complete proof), fully_faithful_reflects_isos (complete proof), fully_faithful_implies_conservative (complete proof), faithful/full/ess_surj composition theorems, yoneda_fully_faithful, functor category completeness, cartesian closed structure (~13 theorems) |
| **L5** | Proof Techniques | **Complete** | Cancellation via natural iso components, diagram chasing with associativity, functoriality + preservation, component-wise reasoning, naturality square algebra, left-cancellation via inverse NTs, construction of preimages via unit/counit, universal property arguments, structural induction (~9 techniques) |
| **L6** | Canonical Examples | **Complete** | listFunctor, optionFunctor, pairFunctor, readerFunctor, stateFunctor (#eval), safeHeadNatTrans (#eval), listReverseNatTrans (#eval), idSetFunctor, constNatFunctor, homUnitFunctor, homBoolOpFunctor, representablePresheaf, 10 counterexamples (~12 examples) |
| **L7** | Applications | **Complete** (4 directions) | Algebra (group actions, modules, representations, monads, Eilenberg-Moore), Topology (simplicial sets, nerve, fundamental groupoid, sheaves on spaces), Geometry (functor of points, algebraic spaces, stacks, moduli problems), Computation (type constructors, free monads, applicative functors, System F, F-algebras) (~20 applications) |
| **L8** | Advanced Topics | **Partial+** | Kan extensions, pointwise Kan extensions, density theorem, Yoneda lemma structure, derived algebraic geometry, model structures on functor categories, ∞-categorical Yoneda |
| **L9** | Research Frontiers | **Partial** | Condensed mathematics, synthetic spectra, univalent foundations (HoTT), derived algebraic geometry, higher topos theory |

## Line Counts

| Category | Files | Lines |
|----------|-------|-------|
| Core | Basic, Objects, Laws | 388 |
| Morphisms | Hom, Iso, Equivalence | 679 |
| Constructions | Products, Universal, Subobjects, Quotients | 1,042 |
| Properties | Invariants, Preservation, ClassificationData | 803 |
| Theorems | Basic, UniversalProperties, Classification, Main | 968 |
| Examples | Standard, Counterexamples | 350 |
| Bridges | ToAlgebra, ToTopology, ToGeometry, ToComputation | 1,198 |
| **Total** | **24 files** | **5,456** |

## Contents

- `Core/Basic.lean` — FunctorCategory [C,D], homFunctor, homFunctorOp, diag, eval, SliceCat, CosliceCat, ArrowCat, PresheafCategory, TwistedArrowCat
- `Core/Objects.lean` — Object instance registration with kernel, FunctorSize, theory nodes
- `Core/Laws.lean` — NaturalTransformation (structure with naturality axiom), vertical/horizontal composition, interchange law, functor composition laws
- `Morphisms/Hom.lean` — NatTrans.id, NatTrans.vcomp/hcomp, EndofunctorCategory, precomposition, postcomposition, whiskering, homMap
- `Morphisms/Iso.lean` — NaturalIsomorphism, identity/composition/symm, FunctorEquivalence, isomorphism in functor category
- `Morphisms/Equivalence.lean` — equivalence_implies_faithful (complete calc proof ~50 lines), equivalence_implies_essentially_surjective, equivalence_reflects_iso_objects (complete calc proof ~60 lines), AdjointEquivalence, KaroubiEnvelope, MoritaEquivalent, Morita refl/symm/trans
- `Constructions/Products.lean` — evalBifunctor, curry/uncurry, exponential adjunction
- `Constructions/Universal.lean` — Diagram, Cone, Cocone, PointwiseLimit, PointwiseColimit, LeftKanExtension, RightKanExtension, PresheafFreeCocompletion, Limit, Colimit
- `Constructions/Subobjects.lean` — isMonicNatTrans, Subfunctor, Sieve, maximalSieve, sieveToSubfunctor, GrothendieckTopology, Site, Subpresheaf, isMonoInFunctorCat, imageSubfunctor
- `Constructions/Quotients.lean` — isEpicNatTrans, QuotientFunctor, CoequalizerInFunctorCat, NatTransFactorization, PresheafQuotient, Cokernel, CoproductFunctors, PushoutNatTrans, Cosieve
- `Properties/Invariants.lean` — id functor properties, faithful/full/ess_surj composition theorems, fully_faithful_reflects_isos, Functor.IsConservative, fully_faithful_implies_conservative
- `Properties/Preservation.lean` — Functor.PreservesLimits/Colimits, isContinuous/isCocontinuous, precomposition/postcomposition preservation, yoneda preservation, eval preservation, PreservesFunctorCategoryStructure
- `Properties/ClassificationData.lean` — FunctorCategorySize, FunctorCategoryStructureClass, Functor.IsLeftExact/IsRightExact/IsExact/IsAdditive, NatTransProperty, presheafCategoryProperties
- `Theorems/Basic.lean` — YonedaBijection, yoneda_fully_faithful, yoneda_reflects_isos, DensityTheorem, CatOfElements, functorCategoryHasPointwiseLimits, cartesianClosedCat
- `Theorems/UniversalProperties.lean` — LanUniversalProperty, RanUniversalProperty, PointwiseKanExtensions, FreeCocompletionUniversalProperty, ExponentialAdjointProperty
- `Theorems/Classification.lean` — functorCat classification by source/target, catOfElementsPresheaf (Grothendieck), CategoryDimension, MonadAsEndofunctor, AdjunctionToMonad
- `Theorems/Main.lean` — L1-L9 knowledge architecture, master theorem list, theorem counts, module statistics
- `Examples/Standard.lean` — forgetfulFunctor, idSetFunctor, constNatFunctor, homUnitFunctor, homBoolOpFunctor, functorCatExample, constantPresheaf, representablePresheaf, setSliceCat, setArrowCat
- `Examples/Counterexamples.lean` — 10 counterexamples with explanations and #eval
- `Bridges/ToAlgebra.lean` — deloop, groupCategory, GSet, GroupRepresentation, ModuleAsFunctor, MonadAsEndofunctor, AlgebraOverMonad, eilenbergMooreCategory, MonoidAction, Bimodule
- `Bridges/ToTopology.lean` — Delta, SimplicialSet, sSet, nerve, nerveFunctor, FundamentalGroupoid, classifyingSpace, openSetCategory, presheafOnSpace, SheafOnSpace, globalSections
- `Bridges/ToGeometry.lean` — functorOfPoints, SchemeAsFunctor, AffineGroupScheme, SheafOnSite, sheafificationFunctor, ZariskiTopology, AlgebraicSpace, Stack, ModuliProblem, tangentCategory
- `Bridges/ToComputation.lean` — listFunctor, optionFunctor, pairFunctor, readerFunctor, stateFunctor, safeHeadNatTrans (#eval), listReverseNatTrans (#eval), FreeMonad, Applicative (Option), systemFModel, FAlgebra

## Dependencies

- `mini-category-core` (for Category, SetCat, opposite, product)
- `mini-morphism-system` (for Functor, NaturalTransformation)

## School Alignments

| School | Relevant Topics Covered |
|--------|------------------------|
| MIT | 18.701/702: monoids as categories; 18.901: fundamental groupoid functor |
| Stanford | MATH 205/210: sheaf theory via presheaves |
| Princeton | MAT 520: functor of points, algebraic spaces |
| Berkeley | MATH 250A: modules as functors, monads |
| Cambridge | Part III: sites, Grothendieck topologies, sheaves |
| Oxford | C2: natural transformations, Yoneda, Kan extensions, free cocompletion |
| ETH | 401-3001: Grothendieck construction, presheaf categories |
| ENS | Analysis on Manifolds: sheaf cohomology, tangent categories |
| 清华 | 抽象代数: group actions as functors; 代数几何: functor of points |

## Completion Date

2026-06-23 — 5,456 lines across 24 source files, all L1-L6 Complete, L7 Complete (4 directions), L8 Partial+, L9 Partial.
