# mini-yoneda-lite

A Lean 4 Lake package implementing the Yoneda lemma and Yoneda embedding in category theory.

## Overview

This package provides:
- Representable functors and presheaf categories
- Yoneda embedding as a functor
- Yoneda lemma: Nat(Hom(X,-), F) ≅ F(X)
- Yoneda embedding is fully faithful
- Uniqueness of representing objects

## Dependencies

- mini-category-core
- mini-functor-core
- mini-natural-transformation

## Build

```bash
lake build
```

## Test

```bash
lean --run Test/Smoke.lean
```

## Structure

- `MiniYonedaLite/Core/` — Core definitions (representable functors, presheaf category, Yoneda embedding)
- `MiniYonedaLite/Theorems/` — The Yoneda lemma and related theorems
- `MiniYonedaLite/Examples/` — Examples and counterexamples
- `MiniYonedaLite/Bridges/` — Connections to algebra, topology, geometry, computation
