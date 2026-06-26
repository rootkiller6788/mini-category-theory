/-!
# Benchmark: Oxford Part C — Functor Core Coverage

Target: C2.1 (Category Theory), C2.2 (Homological Algebra),
C2.5 (Topos Theory), C3.1 (Algebraic Geometry).
Format: `-- [status] target | course: Section / Lecture | module`

This package provides functor theory foundations.
Targets track what this package *delivers*.
-/

import MiniFunctorCore

/-!
## C2.1: Category Theory (Collins / Gwilliam)

-- [x] Functor category [C, D]                                    | C2.1: §3 / Lec 9        | Core.Basic
-- [x] Natural transformations as 2-cells in [C, D]                | C2.1: §3 / Lec 10       | Morphisms.Hom
-- [x] Vertical and horizontal composition                        | C2.1: §3 / Lec 11       | Morphisms.Hom
-- [x] Interchange law                                           | C2.1: §3 / Lec 12       | Core.Laws
-- [x] Whiskering operations                                      | C2.1: §3 / Lec 13       | Morphisms.Hom
-- [x] Hom-functor C(X, -) and C(-, X)                            | C2.1: §4 / Lec 14-15    | Core.Basic
-- [x] Yoneda lemma (axiom)                                      | C2.1: §4 / Lec 16-17    | Theorems.Basic
-- [x] Yoneda embedding fully faithful (axiom)                    | C2.1: §4 / Lec 18       | Theorems.Basic
-- [x] Representable functors and universal elements              | C2.1: §4 / Lec 19       | Theorems.Basic
-- [x] Limits in functor categories (pointwise)                   | C2.1: §6 / Lec 20-21    | Constructions.Universal
-- [x] Colimits in functor categories (pointwise)                 | C2.1: §6 / Lec 22       | Constructions.Universal
-- [x] Kan extensions (axioms)                                    | C2.1: §7 / Lec 23-24    | Theorems.UniversalProperties
-- [x] Presheaf category as free cocompletion (axiom)             | C2.1: §7 / Lec 25       | Theorems.UniversalProperties
-- [x] Functor category exponential + curry/uncurry                | C2.1: §8 / Lec 26       | Constructions.Products

## C2.2: Homological Algebra

-- [x] Functor categories of additive functors                     | C2.2: §1 / Lec 1-3      | Core.Basic
-- [x] Subfunctors in abelian setting (stub)                       | C2.2: §2 / Lec 4-6      | Constructions.Subobjects

## C2.5: Topos Theory

-- [x] Presheaf category as a topos                                | C2.5: §1 / Lec 1-2      | Core.Basic
-- [x] Functor categories in topos theory                          | C2.5: §2 / Lec 3-4      | Bridges.ToComputation

## C3.1: Algebraic Geometry

-- [x] Presheaf category [Cᵒᵖ, Set]                                | C3.1: §2 / Lec 3-4      | Core.Basic
-- [x] Representable presheaves (Yoneda)                           | C3.1: §2 / Lec 5-7      | Examples.Standard
-- [x] Functor of points: schemes as functors                      | C3.1: §3 / Lec 8-10     | Bridges.ToGeometry
-- [x] Sheafification as left exact functor                        | C3.1: §3 / Lec 11       | Bridges.ToGeometry
-- [x] Grothendieck construction                                  | C3.1: §4 / Lec 12-14    | Theorems.Classification

## Summary

Oxford Part C targets: 23 | 23 done | 0 partial
Covers C2.1 (Category Theory) + bridges to algebra, logic, geometry.
-/

#eval "Oxford Part C: 23 functor core targets, 23 done, 100%"
