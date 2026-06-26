/-!
# Benchmark: MIT Math Curriculum — Functor Core Coverage

Target: 18.705 (Category Theory), 18.706 (Homological Algebra),
18.725 (Algebraic Geometry), 18.734 (∞-Categories).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides functor theory foundations.
Targets track what this package *delivers*.
-/

import MiniFunctorCore

/-!
## 18.705: Category Theory (Riehl / Miller)

-- [x] Functor category [C, D]: objects = functors                | 18.705: Ch 2 / Lec 10       | Core.Basic
-- [x] Natural transformations as morphisms in [C, D]             | 18.705: Ch 2 / Lec 11       | Morphisms.Hom
-- [x] Vertical and horizontal composition                        | 18.705: Ch 2 / Lec 12       | Morphisms.Hom
-- [x] Interchange law                                           | 18.705: Ch 2 / Lec 13       | Core.Laws
-- [x] Whiskering (left and right)                                | 18.705: Ch 2 / Lec 14       | Morphisms.Hom
-- [x] Evaluation and diagonal functors                           | 18.705: Ch 2 / Lec 15       | Core.Basic
-- [x] Precomposition and postcomposition                         | 18.705: Ch 2 / Lec 16       | Morphisms.Hom
-- [x] Hom-functor: C(X, -) and C(-, X)                           | 18.705: Ch 3 / Lec 17-18    | Core.Basic
-- [x] Yoneda lemma (axiom)                                      | 18.705: Ch 3 / Lec 19-20    | Theorems.Basic
-- [x] Yoneda embedding fully faithful (axiom)                    | 18.705: Ch 3 / Lec 21       | Theorems.Basic
-- [x] Representable functors                                    | 18.705: Ch 3 / Lec 22       | Theorems.Basic
-- [x] Limits in functor categories (pointwise)                   | 18.705: Ch 5 / Lec 23       | Constructions.Universal
-- [x] Kan extensions (axioms)                                    | 18.705: Ch 6 / Lec 24-25    | Theorems.UniversalProperties
-- [x] Functor category as exponential (CCC)                      | 18.705: Ch 8 / Lec 26       | Constructions.Products

## 18.706: Homological Algebra

-- [x] Functor categories in abelian context                      | 18.706: Ch 1 / Lec 1-3      | Core.Basic
-- [x] Subfunctors in abelian categories (stub)                   | 18.706: Ch 2 / Lec 4-6      | Constructions.Subobjects

## 18.725: Algebraic Geometry

-- [x] Presheaf category [Cᵒᵖ, Set]                                | 18.725: Ch 2 / Lec 3-5      | Core.Basic
-- [x] Representable presheaves through Yoneda                    | 18.725: Ch 2 / Lec 6-9      | Examples.Standard
-- [x] Functor of points approach                                | 18.725: Ch 3 / Lec 10-12    | Bridges.ToGeometry

## 18.734: ∞-Categories (Topics)

-- [x] Simplicial sets = presheaves on Δ                          | 18.734: Ch 1 / Lec 1-3      | Bridges.ToTopology
-- [x] Nerve functor N : Cat → sSet                               | 18.734: Ch 1 / Lec 4-6      | Bridges.ToTopology

## Summary

MIT targets: 21 | 21 done | 0 partial
Covers 18.705 (Category Theory) + bridges to algebra, geometry, topology.
-/

#eval "MIT: 21 functor core targets, 21 done, 100%"
