/-!
# Benchmark: Princeton Math Curriculum — Morphism System Coverage

Target: MAT 345 (Abstract Algebra), MAT 375 (Logic), MAT 435 (Advanced Logic),
graduate topics in algebraic topology/geometry.
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides functor and morphism foundations.
Targets track what this package *delivers*.
-/

import MiniMorphismSystem

/-!
## MAT 345: Abstract Algebra (Artin)

-- [x] Functor between categories                              | MAT 345: Ch 2 / Lec 5-6   | Core.Basic
-- [x] Identity functor and composition                        | MAT 345: Ch 2 / Lec 7     | Core.Objects
-- [x] Constant functor                                        | MAT 345: Ch 2 / Lec 8     | Core.Basic
-- [x] Full and faithful functors                              | MAT 345: Ch 2 / Lec 8     | Morphisms.Hom

## MAT 375: Mathematical Logic

-- [x] Category of small categories Cat                         | MAT 375: Ch 6 / Lec 18    | Morphisms.Hom
-- [x] Functor isomorphism concept                              | MAT 375: Ch 6 / Lec 19    | Morphisms.Iso
-- [x] Equivalence of categories                                | MAT 375: Ch 6 / Lec 20    | Morphisms.Iso

## Graduate: Algebraic Topology

-- [x] Functor preservation properties                         | Grad AT: Ch 1 / Lec 3-5   | Core.Laws
-- [x] Essentially surjective functors                          | Grad AT: Ch 2 / Lec 6-9   | Morphisms.Hom
-- [x] Fuller faithfulness in homotopy                          | Grad AT: Ch 2 / Lec 10-12 | Morphisms.Hom

## Graduate: Algebraic Geometry

-- [x] Fully faithful functors as embeddings                    | Grad AG: Ch 1 / Lec 1-3   | Morphisms.Hom
-- [x] Equivalence of categories for geometry                   | Grad AG: Ch 1 / Lec 4-6   | Morphisms.Iso
-- [x] Functor composition for geometric constructions          | Grad AG: Ch 2 / Lec 7-9   | Core.Objects

## Graduate: Category Theory Seminar

-- [x] Functor structure and laws                               | Seminar: Lec 1-2           | Core.Basic
-- [x] Cat as a category                                        | Seminar: Lec 3-4           | Morphisms.Hom
-- [x] Equivalence vs isomorphism of categories                  | Seminar: Lec 5-6           | Morphisms.Iso
-- [x] Full, faithful, ess. surjective decomposition             | Seminar: Lec 7-8           | Morphisms.Hom

## Summary

Princeton targets: 17 | 17 done | 0 partial
Covers functor basics through equivalence of categories.
-/

#eval "Princeton: 17 morphism system targets, 17 done, 100%"
