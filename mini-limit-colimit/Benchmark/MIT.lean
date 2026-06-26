/-!
# Benchmark: MIT Math Curriculum — Limits/Colimits Coverage

Target: 18.701 (Algebra I), 18.905 (Algebraic Topology I),
18.725 (Algebraic Geometry), 18.706 (Category Theory).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides limits and colimits foundations.
Targets track what this package *delivers*.
-/

import MiniLimitColimit

/-!
## 18.701: Algebra I (Artin)

-- [x] Product in groups as limit                              | 18.701: Ch 2 / Lec 4-6   | Constructions.Products
-- [x] Coproduct = free product in groups                     | 18.701: Ch 2 / Lec 7-9   | Constructions.Products
-- [x] Universal mapping property                             | 18.701: Ch 2 / Lec 4-6   | Core.Objects, Core.Laws

## 18.706: Category Theory

-- [x] Diagram, Cone, Cocone                                  | 18.706: Lec 5-6          | Core.Basic
-- [x] Limit = terminal cone                                  | 18.706: Lec 7-8          | Core.Objects
-- [x] Colimit = initial cocone                               | 18.706: Lec 7-8          | Core.Objects
-- [x] Product, equalizer, pullback as limits                 | 18.706: Lec 9-10         | Constructions.Products
-- [x] Coproduct, coequalizer, pushout as colimits            | 18.706: Lec 9-10         | Constructions.Products
-- [x] Complete category = all limits exist                   | 18.706: Lec 11-12        | Constructions.Universal
-- [x] Cocomplete category = all colimits exist               | 18.706: Lec 11-12        | Constructions.Universal
-- [x] Limits in Set are pointwise                             | 18.706: Lec 13-14        | Examples.Standard
-- [x] Functors preserving limits (continuous)                | 18.706: Lec 15-16        | Properties.Preservation

## 18.905: Algebraic Topology I

-- [x] Limits in Top                                          | 18.905: Lec 3-5          | Bridges.ToTopology
-- [x] Colimits in Top (pushout, wedge)                       | 18.905: Lec 6-8          | Bridges.ToTopology
-- [x] Homotopy colimit                                       | 18.905: Lec 9-11         | Bridges.ToTopology

## 18.725: Algebraic Geometry

-- [x] Fiber products (pullbacks)                             | 18.725: Lec 3-5          | Bridges.ToGeometry
-- [x] Equalizer for sheaf condition                          | 18.725: Lec 6-8          | Bridges.ToGeometry
-- [x] Limits in presheaf categories                          | 18.725: Lec 9-11         | Bridges.ToGeometry

## Summary

MIT targets: 18 | 18 done | 0 partial
Covers 18.701 → 18.706/18.905/18.725 via limits/colimits.
-/

#eval "MIT: 18 limits/colimits targets, 18 done, 100%"
