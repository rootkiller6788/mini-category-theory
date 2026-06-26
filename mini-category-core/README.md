# mini-category-core

Core category theory definitions: Category, SetCat, opposite, product, discrete, codiscrete categories.

## Contents

- `Core/Basic.lean` — Category structure, SetCat, opposite category, product category, DiscCat, CodiscCat
- `Core/Objects.lean` — Object instance registration with kernel
- `Core/Laws.lean` — Category axioms (associativity, identity, functor, naturality), axiom system
- `Constructions/Universal.lean` — Initial, Terminal, Zero objects

## Dependencies

- `mini-object-kernel` (for Object typeclass, TheoryName)
