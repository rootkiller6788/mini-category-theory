# Mini Category Theory

A collection of **from-scratch, zero-dependency Lean 4 implementations** of university-level category theory and functorial mathematics. Each sub-package maps to MIT (and other top-tier university) courses, building the foundations of category theory from first principles using the Lean 4 proof assistant.

## Sub-Packages

| Sub-Package | Topics | Key Courses |
|-------------|--------|-------------|
| [mini-category-core](mini-category-core/) | Categories, objects, morphisms, opposites, products | MIT 18.996, Cambridge Part III |
| [mini-functor-core](mini-functor-core/) | Functors, functor categories, slice/comma categories | MIT 18.996, Princeton MAT 595 |
| [mini-natural-transformation](mini-natural-transformation/) | Natural transformations, natural isomorphisms, functor categories | MIT 18.996, Harvard Math 254 |
| [mini-adjunction](mini-adjunction/) | Adjoint functors, unit/counit, free/forgetful, Galois connections | MIT 18.996, Cambridge Part III |
| [mini-limit-colimit](mini-limit-colimit/) | Limits, colimits, equalizers, pullbacks, completeness | MIT 18.996, Princeton MAT 595 |
| [mini-monad-core](mini-monad-core/) | Monads, Kleisli triples, algebras, monad transformers | MIT 6.821, Oxford CS |
| [mini-morphism-system](mini-morphism-system/) | Factorization systems, (E,M)-factorizations, lifting properties | MIT 18.996, Cambridge Part III |
| [mini-yoneda-lite](mini-yoneda-lite/) | Yoneda lemma, representable functors, universal elements | MIT 18.996, Princeton MAT 595 |

## Design Philosophy

- **Zero external dependencies** -- pure Lean 4, only kernel imports
- **Self-contained sub-packages** -- each has its own `lakefile.lean`, Core/, Morphisms/, Constructions/, Properties/, Theorems/
- **Theory-to-code mapping** -- every module includes inline `#eval` examples and theorem statements
- **Universe-polymorphic** -- categories use `Obj : Type u` and `Hom : Obj -> Obj -> Type v` for flexible universe handling

## Building

Each sub-package is standalone. Build with Lake:

```bash
cd mini-category-core
lake build
lake env lean --run Test/Smoke.lean
```

Requires **Lean 4** and **Lake**.

## Project Structure

```
2. mini-category-theory/
├── mini-category-core/              # Categories, objects, morphisms, products
├── mini-functor-core/               # Functors, functor categories, slice/comma categories
├── mini-natural-transformation/     # Natural transformations, isomorphisms
├── mini-adjunction/                 # Adjoint functors, unit/counit, Galois connections
├── mini-limit-colimit/              # Limits, colimits, equalizers, pullbacks
├── mini-monad-core/                 # Monads, Kleisli triples, algebras
├── mini-morphism-system/            # Factorization systems, lifting properties
├── mini-yoneda-lite/                # Yoneda lemma, representable functors
└── lakefile.lean
```

## License

MIT
