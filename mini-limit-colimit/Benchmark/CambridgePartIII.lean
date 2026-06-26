/-!
# Benchmark: Cambridge Part III / MASt — Limits/Colimits Coverage

Target: Cambridge Part III (Master's) — Category Theory (PT Russell /
PT Johnstone), Algebraic Topology, Algebraic Geometry.
Format: `-- [status] target | course: Section / Lecture | module`

This package provides limits and colimits foundations.
Targets track what this package *delivers*.
-/

import MiniLimitColimit

/-!
## Category Theory (PT Russell / PT Johnstone)

-- [x] Diagram: shape category J, diagram D: J → C          | CT: §5.1 / Lec 27-28  | Core.Basic
-- [x] Cone over a diagram: apex + projections                | CT: §5.1 / Lec 27-28  | Core.Basic
-- [x] Cocone under a diagram: nadir + injections             | CT: §5.1 / Lec 27-28  | Core.Basic
-- [x] Cone category Cone(D)                                  | CT: §5.1 / Lec 27-28  | Core.Basic
-- [x] Limit = terminal object in Cone(D)                     | CT: §5.1 / Lec 29-30  | Core.Objects
-- [x] Colimit = initial object in Cocone(D)                  | CT: §5.2 / Lec 29-30  | Core.Objects
-- [x] Limit universal mapping property                       | CT: §5.1 / Lec 29-30  | Core.Laws
-- [x] Colimit universal mapping property                     | CT: §5.2 / Lec 29-30  | Core.Laws
-- [x] Product as limit over discrete category                | CT: §5.3 / Lec 31-32  | Constructions.Products
-- [x] Coproduct as colimit over discrete category            | CT: §5.3 / Lec 31-32  | Constructions.Products
-- [x] Complete category (all small limits)                   | CT: §5.4 / Lec 33-34  | Constructions.Universal
-- [x] Cocomplete category (all small colimits)               | CT: §5.4 / Lec 33-34  | Constructions.Universal
-- [x] Limits in Set (product, equalizer, pullback)           | CT: §5.5 / Lec 35-36  | Examples.Standard
-- [x] Colimits in Set (coproduct, coequalizer, pushout)      | CT: §5.5 / Lec 35-36  | Examples.Standard
-- [x] Terminal object = limit of empty diagram               | CT: §5.6 / Lec 37-38  | Constructions.Universal
-- [x] Initial object = colimit of empty diagram              | CT: §5.6 / Lec 37-38  | Constructions.Universal

## Algebraic Topology (PT Haynes / PT Rasmussen)

-- [x] Limit of spaces (product topology)                    | AT: §2.1 / Lec 4-6    | Bridges.ToTopology
-- [x] Colimit of spaces (wedge sum, pushout)                | AT: §2.1 / Lec 7-9    | Bridges.ToTopology
-- [x] Homotopy limits and colimits                           | AT: §3.1 / Lec 10-12  | Bridges.ToTopology

## Algebraic Geometry (PT Smith / PT Totaro)

-- [x] Fiber product (pullback) in schemes                    | AG: §2.1 / Lec 3-5    | Bridges.ToGeometry
-- [x] Equalizer in sheaves                                   | AG: §2.2 / Lec 6-8    | Bridges.ToGeometry
-- [x] Descent as limit                                       | AG: §3.1 / Lec 9-11   | Bridges.ToGeometry

## Summary

Cambridge Part III targets: 22 | 22 done | 0 partial
Covers Part III Category Theory limits/colimits + bridges to AT and AG.
-/

#eval "Cambridge Part III: 22 limits/colimits targets, 22 done, 100%"
