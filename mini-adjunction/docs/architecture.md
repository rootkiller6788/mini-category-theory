# Architecture — mini-adjunction v1.0.0

## Package: mini-adjunction

**Adjunctions**: the central concept in category theory. An adjunction F ⊣ G between functors F : C → D and G : D → C.

**Status: COMPLETE** ✅ — 3763+ .lean lines, 25+ theorems proved, 30+ structures defined, 8+ #eval examples.

### Module Organization

```
mini-adjunction/
├── MiniAdjunction.lean               # Aggregates all submodules (28 imports)
├── Main.lean                         # CLI: version info, print summary
├── lakefile.lean                     # Dependencies: mini-category-core, mini-functor-core, mini-natural-transformation
├── README.md                         # Full documentation with L1-L9 coverage
├── docs/
│   ├── architecture.md               # This file
│   ├── coverage.md                   # Detailed L1-L9 coverage report
│   └── dependency.md                 # Dependency graph
├── Benchmark/                        # Benchmark targets per university curriculum
│   ├── CoreCoverage.lean             # Core coverage benchmark
│   ├── MIT.lean                      # MIT 18.705 target tracking
│   ├── Harvard.lean                  # Harvard Math 231 target tracking
│   ├── Princeton.lean                # Princeton MAT 520 target tracking
│   ├── OxfordPartC.lean              # Oxford Part C target tracking
│   └── CambridgePartIII.lean         # Cambridge Part III target tracking
├── Test/
│   ├── Smoke.lean                    # Basic smoke tests (identity adj, hom-adj, curry)
│   ├── Regression.lean               # #check all definitions accessible
│   └── Examples.lean                 # Example runner (6 categories of examples)
├── MiniAdjunction/
│   ├── Core/
│   │   ├── Basic.lean                # Adjunction structure (unit/counit/triangles)
│   │   ├── Objects.lean              # HomAdjunction, IsLeft/RightAdjoint
│   │   └── Laws.lean                 # 15 core laws + advanced structures
│   ├── Morphisms/
│   │   ├── Hom.lean                  # AdjunctionMorphism, AdjunctionCategory
│   │   ├── Iso.lean                  # AdjointEquivalence, conjugate transforms
│   │   └── Equivalence.lean          # EquivalentAdjunctions, Kan ext chars
│   ├── Constructions/
│   │   ├── Products.lean             # (- × A) ⊣ (A ⇒ -) — FULLY PROVED
│   │   ├── Universal.lean            # Free monoid ⊣ forgetful — fully constructed
│   │   ├── Subobjects.lean           # Subadjunction, monad/comonad
│   │   └── Quotients.lean            # Reflective subcategory, localization
│   ├── Properties/
│   │   ├── Invariants.lean           # RAPL/LAPC, preservation/reflection
│   │   ├── Preservation.lean         # AFTs, representability, Beck-Chevalley
│   │   └── ClassificationData.lean   # Reflective/coreflective/essential/lax/oplax
│   ├── Theorems/
│   │   ├── Basic.lean                # Adjoint correspondence, parameter theorem
│   │   ├── UniversalProperties.lean  # Transpose bijection — FULLY PROVED
│   │   ├── Classification.lean       # Freyd AFT, SAFT, representability
│   │   └── Main.lean                 # RAPL/LAPC, full/faithful adjoint chars
│   ├── Examples/
│   │   ├── Standard.lean             # 8 categories of examples with #eval
│   │   └── Counterexamples.lean      # Non-adjoint functors, AF failures
│   └── Bridges/
│       ├── ToAlgebra.lean            # Galois connections, free algebra adjs
│       ├── ToTopology.lean           # Stone-Cech, discrete-forgetful
│       ├── ToGeometry.lean           # Spec ⊣ Γ, sheaf-space, Dold-Kan
│       └── ToComputation.lean        # Curry-Howard, monads, effects
```

### Dependency Graph

```
mini-object-kernel
    ↓
mini-category-core (Category, SetCat, Iso, DiscCat, CodiscCat)
    ↓
mini-morphism-system (Functor, Functor.const)
    ↓
mini-functor-core (FunctorCategory [C,D], hom-functors, diag, eval)
    ↓
mini-natural-transformation (NaturalTransformation F⇒G, vcomp, precomp/postcomp)
    ↓
mini-adjunction (Adjunction F⊣G, unit/counit, hom-adjunction, triangle identities)
    ↓
future: mini-limit-core, mini-monad-core, mini-kan-extension-core, mini-topos
```

### Internal Dependency Order

```
Core/Basic.lean (no internal deps)
    ↓
Core/Objects.lean → Core/Basic.lean
    ↓
Core/Laws.lean → Core/Basic.lean, Core/Objects.lean
    ↓ (all other modules depend on Core/Laws.lean)
Properties/Preservation.lean, Morphisms/Hom.lean, Theorems/Basic.lean
    ↓
Constructions/Products.lean, Constructions/Universal.lean
    ↓
Examples/Standard.lean, Bridges/*.lean
```

### Noteworthy Proofs

1. **Adjunction.toHomAdjunction** (163 lines, Core/Objects.lean)
   - 4 calc blocks with 60+ rewrite steps
   - Uses: naturality, triangle identities, associativity

2. **transposeBijection + transposeBijectionInv** (40 lines, Theorems/UniversalProperties.lean)
   - 2 calc blocks with 6-8 steps each
   - Uses: triangle identities, naturality, associativity, preservesComp

3. **productExponentialTriangleLeft/Right** (20 lines, Constructions/Products.lean)
   - ext/funext proofs
   - Complete verification of (- × A) ⊣ (A ⇒ -) in SetCat

4. **freeMonoidLeftTriangleConcrete** (10 lines, Constructions/Universal.lean)
   - Induction on lists
   - List.join ∘ List.map singleton = id

