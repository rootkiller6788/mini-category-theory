# mini-morphism-system — Architecture

## Layer Map

```
┌─────────────────────────────────────────────────────────┐
│                    7. Bridges                           │
│  ToAlgebra  │  ToTopology  │  ToGeometry  │  ToComputation │
├─────────────────────────────────────────────────────────┤
│              6. Examples                                │
│         Standard    │    Counterexamples                │
├─────────────────────────────────────────────────────────┤
│              5. Theorems                                │
│  Basic  │  UniversalProperties  │  Classification  │  Main │
├─────────────────────────────────────────────────────────┤
│              4. Properties                              │
│  Invariants  │  Preservation  │  ClassificationData     │
├─────────────────────────────────────────────────────────┤
│              3. Constructions                           │
│  Subobjects  │  Quotients  │  Products  │  Universal    │
├─────────────────────────────────────────────────────────┤
│              2. Morphisms                               │
│  Hom (Functor Props)  │  Iso (FunctorIso)  │  Equivalence │
├─────────────────────────────────────────────────────────┤
│              1. Core                                    │
│  Basic (Functor)  │  Objects (id/comp)  │  Laws (Proofs) │
└─────────────────────────────────────────────────────────┘
```

## Design Decisions

1. **Functor as structure.** A `Functor` bundles `mapObj`, `mapHom`, `preservesId`,
   and `preservesComp` as a record. Parallel to the `Category` structure.

2. **Notation.** `F[X]` for object map and `F⟦f⟧` for morphism map via Lean notation.

3. **Functor properties as Prop.** `IsFull`, `IsFaithful`, `IsFullyFaithful`, and
   `IsEssentiallySurjective` are `Prop` predicates on functors.

4. **Cat as a Category.** The category of small categories has `Obj := Category` and
   `Hom := Functor`, with `Functor.id` and `Functor.comp`.

5. **Equivalence via forth/back.** An `Equivalence` bundles two functors with natural
   isomorphisms, following the standard definition.

## Dependency Hierarchy

```
Core/Basic       (no deps)
Core/Objects     → Core/Basic
Core/Laws        → Core/Basic, Core/Objects

Morphisms/Hom    → Core/Basic, Core/Objects
Morphisms/Iso    → Core/Basic, Core/Objects
Morphisms/Equivalence → Morphisms/Iso

Constructions/*  → Core/Basic
Properties/*     → Core/Basic
Theorems/*       → Core/Basic
Examples/*       → Core/Basic
Bridges/*        → Core/Basic
```
