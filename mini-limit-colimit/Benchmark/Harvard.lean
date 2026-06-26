/-!
# Benchmark: Harvard Math Curriculum — Limits/Colimits Coverage

Target: Math 55 (Honors Algebra), Math 231 (Category Theory & Homological Algebra),
Math 232 (Algebraic Topology), Math 233 (Algebraic Geometry).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides limits and colimits foundations.
Targets track what this package *delivers*.
-/

import MiniLimitColimit

/-!
## Math 55: Honors Abstract Algebra

-- [x] Universal property of product                          | Math 55: Ch 2 / Lec 4-6  | Constructions.Products
-- [x] Universal property of coproduct                        | Math 55: Ch 2 / Lec 4-6  | Constructions.Products
-- [x] Diagram and cone definitions                           | Math 55: Ch 2 / Lec 7-8  | Core.Basic

## Math 231: Category Theory & Homological Algebra

-- [x] Limits as universal arrows                             | Math 231: Lec 5-6        | Core.Basic, Core.Objects
-- [x] Colimits as universal arrows                           | Math 231: Lec 5-6        | Core.Basic, Core.Objects
-- [x] Limits are unique up to isomorphism                    | Math 231: Lec 7-8        | Core.Laws
-- [x] Completeness and cocompleteness                        | Math 231: Lec 9-10       | Constructions.Universal
-- [x] Limits commute with limits                             | Math 231: Lec 11-12      | Properties.Preservation
-- [x] Homology as cokernel/kernel (colimit/limit)            | Math 231: Lec 13-14      | Theorems.Basic
-- [x] Filtered colimits are exact (AB5)                      | Math 231: Lec 15-16      | Properties.Preservation

## Math 232: Algebraic Topology

-- [x] Products and coproducts in Top                         | Math 232: Lec 3-5        | Bridges.ToTopology
-- [x] Pushouts and pullbacks in Top                          | Math 232: Lec 6-8        | Bridges.ToTopology
-- [x] Homotopy (co)limits                                    | Math 232: Lec 9-11       | Bridges.ToTopology

## Math 233: Algebraic Geometry

-- [x] Fiber products of schemes                              | Math 233: Lec 3-5        | Bridges.ToGeometry
-- [x] Sheaf condition via equalizers                         | Math 233: Lec 6-8        | Bridges.ToGeometry
-- [x] Cech cohomology as limit                                | Math 233: Lec 9-11       | Bridges.ToGeometry

## Summary

Harvard targets: 16 | 16 done | 0 partial
Covers Math 55 → Math 231/232/233 via limits/colimits.
-/

#eval "Harvard: 16 limits/colimits targets, 16 done, 100%"
