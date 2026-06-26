/-!
# Benchmark: Oxford Part C / MMath — Limits/Colimits Coverage

Target: Oxford Part C (4th year) — Category Theory (C2.2),
Algebraic Topology (C3.2), Algebraic Geometry (C3.3).
Format: `-- [status] target | course: Section / Lecture | module`

This package provides limits and colimits foundations.
Targets track what this package *delivers*.
-/

import MiniLimitColimit

/-!
## C2.2: Category Theory

-- [x] Diagram = functor from indexing category               | C2.2: §2.1 / Lec 3-4    | Core.Basic
-- [x] Cone and cocone definitions                            | C2.2: §2.1 / Lec 3-4    | Core.Basic
-- [x] Limit = universal cone                                 | C2.2: §2.2 / Lec 5-6    | Core.Objects
-- [x] Colimit = universal cocone                              | C2.2: §2.2 / Lec 5-6    | Core.Objects
-- [x] Product as limit, coproduct as colimit                  | C2.2: §2.3 / Lec 7-8    | Constructions.Products
-- [x] Equalizer and coequalizer                              | C2.2: §2.3 / Lec 7-8    | Constructions.Products
-- [x] Pullback and pushout                                   | C2.2: §2.4 / Lec 9-10   | Constructions.Products
-- [x] Complete and cocomplete categories                      | C2.2: §2.5 / Lec 11-12  | Constructions.Universal
-- [x] Limits commute (limit of limits)                        | C2.2: §2.5 / Lec 11-12  | Properties.Preservation
-- [x] Limits in functor categories are pointwise             | C2.2: §2.6 / Lec 13-14  | Examples.Standard
-- [x] Right adjoints preserve limits                          | C2.2: §3.1 / Lec 15-16  | Theorems.Basic
-- [x] Left adjoints preserve colimits                         | C2.2: §3.1 / Lec 15-16  | Theorems.Basic
-- [x] Adjoint functor theorem via limits                      | C2.2: §3.2 / Lec 17-18  | Theorems.UniversalProperties

## C3.2: Algebraic Topology

-- [x] Products and coproducts in Top                         | C3.2: §1.2 / Lec 2-4    | Bridges.ToTopology
-- [x] Pushout = attaching map construction                   | C3.2: §1.3 / Lec 5-7    | Bridges.ToTopology
-- [x] Homotopy limits/colimits                               | C3.2: §2.2 / Lec 8-10   | Bridges.ToTopology

## C3.3: Algebraic Geometry

-- [x] Fiber product in schemes                               | C3.3: §2.1 / Lec 2-4    | Bridges.ToGeometry
-- [x] Sheaf condition via equalizer diagram                  | C3.3: §2.2 / Lec 5-7    | Bridges.ToGeometry
-- [x] Limits in Ab (Grothendieck's AB axioms)                | C3.3: §3.2 / Lec 8-10   | Bridges.ToGeometry

## Summary

Oxford Part C targets: 19 | 19 done | 0 partial
Covers C2.2 Category Theory limits/colimits + bridges to AT and AG.
-/

#eval "Oxford Part C: 19 limits/colimits targets, 19 done, 100%"
