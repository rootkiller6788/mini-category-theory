# mini-morphism-system — Dependency Graph

## Internal Dependencies

```
Core/Basic.lean       (no deps)
Core/Objects.lean     → Core/Basic
Core/Laws.lean        → Core/Basic, Core/Objects

Morphisms/Hom.lean    → Core/Basic, Core/Objects
Morphisms/Iso.lean    → Core/Basic, Core/Objects
Morphisms/Equivalence → Morphisms/Iso

Constructions/Subobjects  → Core/Basic
Constructions/Quotients   → Core/Basic
Constructions/Products    → Core/Basic
Constructions/Universal   → Core/Basic

Properties/Invariants       → Core/Basic
Properties/Preservation     → Core/Basic
Properties/ClassificationData → Core/Basic

Theorems/Basic               → Core/Basic
Theorems/UniversalProperties → Core/Basic
Theorems/Classification      → Core/Basic
Theorems/Main                → Core/Basic

Examples/Standard       → Core/Basic
Examples/Counterexamples → Core/Basic

Bridges/ToAlgebra       → Core/Basic
Bridges/ToTopology      → Core/Basic
Bridges/ToGeometry      → Core/Basic
Bridges/ToComputation   → Core/Basic
```

## External Dependencies

- `mini-category-core` — provides `Category` structure, `SetCat`, core laws
- `mini-object-kernel` — transitive dependency via `mini-category-core`

## Import Graph (condensed)

```
mini-category-core ← Core/Basic ← Core/Objects ← Core/Laws
                               ↓
            ← Morphisms/Hom ← Morphisms/Iso ← Morphisms/Equivalence

All stubs (Constructions, Properties, Theorems, Examples, Bridges)
depend on Core/Basic only.
```
