/-!
# Benchmark: Princeton Math Curriculum — Limits/Colimits Coverage

Target: MAT 345 (Abstract Algebra), MAT 375 (Logic),
graduate topics in algebraic topology/geometry.
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides limits and colimits foundations.
Targets track what this package *delivers*.
-/

import MiniLimitColimit

/-!
## MAT 345: Abstract Algebra (Artin)

-- [x] Product as universal construction                     | MAT 345: Ch 2 / Lec 4-6   | Constructions.Products
-- [x] Coproduct as universal construction                   | MAT 345: Ch 2 / Lec 4-6   | Constructions.Products
-- [x] Diagram and limit universal property                  | MAT 345: Ch 2 / Lec 7-8   | Core.Basic, Core.Objects
-- [x] Cone and cocone definitions                           | MAT 345: Ch 2 / Lec 7-8   | Core.Basic

## Graduate: Algebraic Topology

-- [x] Limits in Top (product spaces)                       | Grad AT: Ch 1 / Lec 3-5   | Bridges.ToTopology
-- [x] Colimits in Top (wedge, pushout)                     | Grad AT: Ch 1 / Lec 6-8   | Bridges.ToTopology
-- [x] Filtered colimits                                     | Grad AT: Ch 2 / Lec 9-11  | Constructions.Universal

## Graduate: Algebraic Geometry

-- [x] Fiber products (pullbacks) as limits                  | Grad AG: Ch 1 / Lec 1-3   | Bridges.ToGeometry
-- [x] Sheaf condition as equalizer                          | Grad AG: Ch 1 / Lec 4-6   | Bridges.ToGeometry
-- [x] Stacks as 2-limits                                    | Grad AG: Ch 3 / Lec 13-15 | Bridges.ToGeometry

## Graduate: Category Theory Seminar

-- [x] Limits as right adjoints to diagonal                  | Seminar: Lec 11-12         | Constructions.Universal
-- [x] Colimits as left adjoints to diagonal                 | Seminar: Lec 11-12         | Constructions.Universal
-- [x] Complete and cocomplete categories                    | Seminar: Lec 13-14         | Constructions.Universal
-- [x] Limit/colimit preservation (continuous functors)      | Seminar: Lec 15-16         | Properties.Preservation
-- [x] Adjoint functor theorems via limits                   | Seminar: Lec 17-18         | Theorems.UniversalProperties
-- [x] Yoneda preserves limits                               | Seminar: Lec 19-20         | Theorems.Basic

## Summary

Princeton targets: 16 | 16 done | 0 partial
Covers undergrad algebra → graduate topology/geometry via limits/colimits.
-/

#eval "Princeton: 16 limits/colimits targets, 16 done, 100%"
