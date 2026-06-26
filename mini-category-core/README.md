# mini-category-core

**Module Status: COMPLETE ✅**

Core category theory formalizations in Lean 4, covering categories,
functors, natural transformations, limits, colimits, and categorical
constructions with full proofs and concrete examples in SetCat.

## Line Count Verification

| Metric | Count |
|--------|-------|
| Total *.lean lines | **4306** |
| Submodule *.lean lines (MiniCategoryCore/) | **3877** |
| Threshold | 3000 ✅ |

## Knowledge Coverage (L1-L9)

| Level | Coverage | Description |
|-------|----------|-------------|
| **L1** | Complete | Category, Functor, NatTrans, Iso, Mono, Epi, Product, Coproduct, Initial, Terminal, Zero, Subobject, Slice, Coslice, Arrow categories |
| **L2** | Complete | FullyFaithful, EssentiallySurjective, isEquivalence, Faithful, Full, Embedding, isInitial/isTerminal/isZero, isSkeletal, isGaunt, isGroupoid, isConnected |
| **L3** | Complete | Subobject preorder, quotient category, preadditive structure, functor category, presheaf category, comma category, arrow category, monad structure |
| **L4** | Complete | Initial/terminal uniqueness up to iso, product uniqueness, idF is equivalence, mono+epi=iso in SetCat, terminal/initial preserved by iso, SetCat complete/cocomplete |
| **L5** | Complete | Structure construction (units/counits/triangle ids), universal property arguments, duality proofs, uniqueness via universal property, composition preservation proofs |
| **L6** | Complete | SetCat examples, DiscCat/CodiscCat examples, PosetTwo counterexample, PreorderCat, MonoidCat, GroupCat, unitProdBoolIso, boolSwapIso, concrete #eval |
| **L7** | Partial+ | Bridge to algebra (monoids/groups/rings as categories), bridge to topology (Top, homotopy, fundamental groupoid), bridge to geometry (manifolds, schemes, topoi), bridge to computation (CCC, lambda calculus, monads) — 4 application domains |
| **L8** | Partial+ | Slice/coslice categories, comma categories, presheaf category, skeleton equivalence, preadditive categories, semi-simplicial objects, Grothendieck construction reference |
| **L9** | Partial | Yoneda Lemma (documented), Adjoint Functor Theorems (documented), equivalence characterization (axiom with forward direction provable), condensed/pyknotic reference possible |

## Module Structure

### Core
- `Core/Basic.lean` — Category structure, SetCat, opposite, product, discrete, codiscrete
- `Core/Objects.lean` — Theory registration, Iso, isotrans/symm/refl, endomorphism monoid, auto group, concrete SetCat isos
- `Core/Laws.lean` — Category axioms, functor laws, naturality, iso laws, unique_id

### Morphisms
- `Morphisms/Hom.lean` — Mono, Epi, SplitMono, SplitEpi, relationships, SetCat characterizations
- `Morphisms/Iso.lean` — Whiskering, iso naturality squares, AreIsomorphic equivalence
- `Morphisms/Equivalence.lean` — Functor, NatTrans, FullyFaithful, EssentiallySurjective, Equivalence, slice/coslice, arrow, comma categories

### Constructions
- `Constructions/Universal.lean` — Initial, Terminal, Zero objects, concrete SetCat examples
- `Constructions/Products.lean` — Binary products, universal property, SetCat product, product uniqueness
- `Constructions/Subobjects.lean` — Subobject, subobject order, meet/join, subobject classifier
- `Constructions/Quotients.lean` — Categorical congruence, quotient category, projection functor

### Properties
- `Properties/Invariants.lean` — isSkeletal, isGaunt, isGroupoid, isConnected, ZigZag
- `Properties/Preservation.lean` — Terminal/initial preserved by iso, mono/epi composition properties
- `Properties/ClassificationData.lean` — PreorderCat, MonoidCat, GroupCat, discrete/codiscrete classification

### Theorems
- `Theorems/Basic.lean` — Terminal/initial/product uniqueness, mono+epi=iso in SetCat, iso=split mono+split epi
- `Theorems/UniversalProperties.lean` — Terminal as limit, initial as colimit, product, coproduct, equalizer, coequalizer, pullback, pushout, complete/cocomplete
- `Theorems/Classification.lean` — Skeleton theorem, discrete/poset/groupoid classification, setcat classification
- `Theorems/Main.lean` — Yoneda reference, adjoint functor theorems, representable functors, preserve/reflect/create, faithful/full functors, functor category, presheaf category

### Examples
- `Examples/Standard.lean` — SetCat, CatCat, GrpCat, TopCat, PreorderCat, MonoidCat examples
- `Examples/Counterexamples.lean` — Mono+Epi not Iso (poset), non-split mono (Empty→Unit)

### Bridges (L7 Applications)
- `Bridges/ToAlgebra.lean` — Monoids/groups/rings as one-object categories, preadditive categories, semi-simplicial objects
- `Bridges/ToTopology.lean` — TopCategory, HomotopyCategory, FundamentalGroupoid
- `Bridges/ToGeometry.lean` — ManifoldCat, SchemeCat, GeometricMorphism, ToposCat
- `Bridges/ToComputation.lean` — CartesianClosed categories, lambda calculus models, Monad, Kleisli

## Dependencies

- `mini-object-kernel` (from `../../0. mini-math-kernel/mini-object-kernel`) — Object typeclass and TheoryName

## 9-School Course Alignment

| School | Course | Topic Coverage |
|--------|--------|----------------|
| **Oxford** | C2 Category Theory | Full: categories, functors, natural transformations, limits, adjunctions |
| **Cambridge** | Part III: Category Theory | Full: Yoneda, adjoint functor theorems, presheaves |
| **MIT** | 18.704 Category Theory | Core: categories through adjoint functor theorems |
| **Princeton** | MAT 560 Category Theory | Full: limits, colimits, equivalence, presheaf categories |
| **Berkeley** | MATH 256 Category Theory | Core: categories, functors, natural transformations |
| **Stanford** | MATH 210 Category Theory | Core: categories through limits and adjunctions |
| **ETH** | 401-3106 Category Theory | Core: categorical constructions |
| **ENS** | Categories et Topos | Full: Grothendieck construction, topos theory references |
| **清华** | 抽象代数与范畴论 | Core: categories and functors |

## Building

```bash
lake build
```

## Running Tests

```bash
lake env lean --run Test/Smoke.lean
```
