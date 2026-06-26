# Knowledge Graph — mini-morphism-system

## L1: Core Definitions (Complete)
| Definition | File | Status |
|-----------|------|--------|
| `Functor` (mapObj, mapHom, preservesId, preservesComp) | Core/Basic.lean | ✓ |
| `Functor.const` | Core/Basic.lean | ✓ |
| `Functor.id` | Core/Objects.lean | ✓ |
| `Functor.comp` | Core/Objects.lean | ✓ |
| `Iso` (fwd, rev, fwd_rev, rev_fwd) | Core/Objects.lean | ✓ |
| `MorphismClass` | Core/Objects.lean | ✓ |
| `HasLLP` (left lifting property `⋔`) | Core/Objects.lean | ✓ |
| `Orthogonal` (`⊥`) | Core/Objects.lean | ✓ |
| `FactorizationSystem` (E, M, factorization, orthogonal, containsIso) | Core/Objects.lean | ✓ |
| `LiftingSystem` (L, R, lifting) | Core/Objects.lean | ✓ |
| `Functor.IsFull` | Morphisms/Hom.lean | ✓ |
| `Functor.IsFaithful` | Morphisms/Hom.lean | ✓ |
| `Functor.IsFullyFaithful` | Morphisms/Hom.lean | ✓ |
| `Functor.IsEssentiallySurjective` | Morphisms/Hom.lean | ✓ |
| `Cat` (category of small categories) | Morphisms/Hom.lean | ✓ |
| `FunctorIso` (natural isomorphism with naturality) | Morphisms/Iso.lean | ✓ |
| `Equivalence` (forth, back, unitIso, counitIso, triangle identities) | Morphisms/Iso.lean | ✓ |
| `isEpi`, `isMono` | Properties/ClassificationData.lean | ✓ |
| `isSplitEpi`, `isSplitMono` | Properties/ClassificationData.lean | ✓ |
| `isStrongEpi` | Properties/ClassificationData.lean | ✓ |
| `isEffectiveEpi` | Properties/ClassificationData.lean | ✓ |
| `ModelStructureData` | Properties/ClassificationData.lean | ✓ |
| `isStableUnderComposition/Pushout/Pullback/Retracts` | Properties/Invariants.lean | ✓ |
| `SaturatedClass` | Properties/Invariants.lean | ✓ |
| `MorphismClass.saturation` | Constructions/Universal.lean | ✓ |
| `CompClosure`, `CompClosureM` | Constructions/Universal.lean | ✓ |
| `MorphismClass.sub/fullOn/restrict` | Constructions/Subobjects.lean | ✓ |
| `SubobjectOfMorphism`, `ImageFactorization` | Constructions/Subobjects.lean | ✓ |
| `SubFactorizationSystem` | Constructions/Subobjects.lean | ✓ |
| `MorphismClass.quotient` | Constructions/Quotients.lean | ✓ |
| `CofibrantReplacement` | Constructions/Quotients.lean | ✓ |
| `ProjectionSystem` | Constructions/Quotients.lean | ✓ |
| `MorphismClass.prod` | Constructions/Products.lean | ✓ |
| `FactorizationSystem.prod` | Constructions/Products.lean | ✓ |
| `LiftingSystem.prod` | Constructions/Products.lean | ✓ |
| `HasEpiMonoFactorization` | Theorems/Basic.lean | ✓ |
| `OrthogonalFactorizationSystem` | Theorems/Classification.lean | ✓ |
| `WeakFactorizationSystem` | Theorems/Classification.lean | ✓ |
| `ModelCategory` | Theorems/Classification.lean | ✓ |
| `UniversalFactorizationProperty` | Theorems/UniversalProperties.lean | ✓ |
| `InitialFactorization`, `TerminalFactorization` | Theorems/UniversalProperties.lean | ✓ |

## L2: Core Concepts (Complete)
| Concept | File | Status |
|---------|------|--------|
| Functor preserves identity and composition | Core/Laws.lean | ✓ |
| Functor composition associativity and identity | Core/Laws.lean | ✓ |
| Functor preserves isomorphisms | Core/Laws.lean | ✓ |
| Fully faithful functors reflect isomorphisms | Core/Laws.lean | ✓ |
| Iso conjugation preserves invertibility | Core/Laws.lean | ✓ |
| Iso inverse uniqueness | Core/Laws.lean | ✓ |
| Full + faithful + essentially surjective ↔ equivalence | Morphisms/Equivalence.lean | ✓ |
| Equivalence symmetry, reflexivity, transitivity | Morphisms/Equivalence.lean | ✓ |
| Orthogonal diagonal uniqueness | Core/Laws.lean | ✓ |
| Factorization comparison theorem | Core/Laws.lean | ✓ |
| Orthogonal factorization unique iso theorem | Core/Laws.lean | ✓ |

## L3: Math Structures (Complete)
| Structure | File | Status |
|-----------|------|--------|
| Factorization System (E, M) | Core/Objects.lean | ✓ |
| Lifting System | Core/Objects.lean | ✓ |
| Orthogonal Factorization System | Theorems/Classification.lean | ✓ |
| Weak Factorization System | Theorems/Classification.lean | ✓ |
| Model Category (two WFS) | Theorems/Classification.lean | ✓ |
| Equivalence of Categories | Morphisms/Iso.lean | ✓ |
| Functor Category (Cat) | Morphisms/Hom.lean | ✓ |
| Stable Factorization System | Properties/Invariants.lean | ✓ |
| Saturated Class | Properties/Invariants.lean | ✓ |
| Projection System | Constructions/Quotients.lean | ✓ |
| Generated Factorization System | Constructions/Universal.lean | ✓ |
| Restricted Factorization System | Constructions/Subobjects.lean | ✓ |

## L4: Fundamental Theorems (Complete)
| Theorem | File | Status |
|---------|------|--------|
| SetCat has (epi, mono) factorization | Theorems/Basic.lean | ✓ |
| (Epi, mono) factorization is unique up to iso | Core/Laws.lean | ✓ |
| Equivalence ↔ fully faithful + essentially surjective | Morphisms/Equivalence.lean | ✓ |
| Epi/mono closure under composition | Theorems/Basic.lean | ✓ |
| Any functor preserves isomorphisms | Core/Laws.lean | ✓ |
| Orthogonal FS: E = epis, M = monos | Theorems/Classification.lean | ✓ |
| Factorization universal property | Theorems/UniversalProperties.lean | ✓ |
| HasEpiMonoFactorization → FactorizationSystem | Theorems/Main.lean | ✓ |
| SetCat (epi, mono) is a factorization system | Theorems/Main.lean | ✓ |
| Product factorization system | Constructions/Products.lean | ✓ |

## L5: Proof Techniques (Complete)
| Technique | Example | File |
|-----------|---------|------|
| Calc block (associative rewriting) | Iso conjugation | Core/Laws.lean |
| Diagonal argument (uniqueness) | Orthogonal factorization uniqueness | Core/Laws.lean |
| Naturality reasoning | Equivalence fully faithful proof | Morphisms/Equivalence.lean |
| Structural induction on closures | CompClosure | Constructions/Universal.lean |
| Component-wise reasoning | Product factorization | Constructions/Products.lean |
| Faithfulness inversion | Fully faithful reflection | Core/Laws.lean |

## L6: Canonical Examples (Complete)
| Example | File | Status |
|---------|------|--------|
| Squaring function factorization | Examples/Standard.lean | ✓ |
| Constant morphism factorization | Examples/Standard.lean | ✓ |
| Product projection (split epi) | Examples/Standard.lean | ✓ |
| Identity factorization | Examples/Standard.lean | ✓ |
| Bool inclusion factorization | Examples/Standard.lean | ✓ |
| SetCat (epi, mono) FS | Examples/Standard.lean | ✓ |
| Discrete category FS | Examples/Standard.lean | ✓ |
| Product category FS | Examples/Standard.lean | ✓ |
| Codiscrete non-unique factorization | Examples/Counterexamples.lean | ✓ |
| 3-object category no lifting | Examples/Counterexamples.lean | ✓ |
| Empty/trivial lifting system vs FS | Examples/Counterexamples.lean | ✓ |
| Constant functor examples | Morphisms/Hom.lean | ✓ |

## L7: Applications (Partial+, 4 directions)
| Application | File | Status |
|-------------|------|--------|
| Algebra: projective/injective objects | Bridges/ToAlgebra.lean | ✓ |
| Algebra: exact sequences, resolutions | Bridges/ToAlgebra.lean | ✓ |
| Topology: Hurewicz cofibration, Serre fibration | Bridges/ToTopology.lean | ✓ |
| Topology: model structures on Top | Bridges/ToTopology.lean | ✓ |
| Geometry: smooth/proper factorization | Bridges/ToGeometry.lean | ✓ |
| Geometry: Stein factorization, Zariski | Bridges/ToGeometry.lean | ✓ |
| Computation: type factorization | Bridges/ToComputation.lean | ✓ |
| Computation: data refinement, Hoare logic | Bridges/ToComputation.lean | ✓ |

## L8: Advanced Topics (Partial+, 2 topics)
| Topic | File | Status |
|-------|------|--------|
| Orthogonal factorization systems | Theorems/Classification.lean | ✓ |
| Weak factorization systems + model categories | Theorems/Classification.lean | ✓ |
| Composition of equivalences | Morphisms/Equivalence.lean | Partial (proof sketch) |
| Generated/free factorization systems | Constructions/Universal.lean | ✓ |
| Projection and quotient systems | Constructions/Quotients.lean | ✓ |

## L9: Research Frontiers (Partial, documented)
| Topic | Documentation | Status |
|-------|---------------|--------|
| ∞-categories and homotopy factorization | Benchmark files | Documented |
| Condensed mathematics | Not implemented | Planned |
| Univalent foundations (HoTT) | Not implemented | Planned |
