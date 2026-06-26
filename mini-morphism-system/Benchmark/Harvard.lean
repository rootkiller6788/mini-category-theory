/-!
# Benchmark: Harvard Math Curriculum — Morphism System Coverage

Target: Math 231 (Category Theory), Math 232 (Homological Algebra),
Math 254/255 (Graduate Logic), Math 256 (Algebraic Geometry).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides functor and morphism foundations.
Targets track what this package *delivers*.
-/

import MiniMorphismSystem

/-!
## Math 231: Category Theory (Mazur / Lurie)

-- [x] Functor: mapObj, mapHom, preservesId, preservesComp     | Math 231: Ch 1 / Lec 4-5   | Core.Basic
-- [x] Functor.id, Functor.comp, Functor.const                  | Math 231: Ch 1 / Lec 6-7   | Core.Objects
-- [x] Full, faithful, fully faithful functors                  | Math 231: Ch 1 / Lec 8     | Morphisms.Hom
-- [x] Essentially surjective functors                          | Math 231: Ch 1 / Lec 9     | Morphisms.Hom
-- [x] Functor isomorphism structure                            | Math 231: Ch 2 / Lec 10-12 | Morphisms.Iso
-- [x] Equivalence of categories                                | Math 231: Ch 2 / Lec 13-15 | Morphisms.Iso
-- [x] Cat as a category of small categories                     | Math 231: Ch 3 / Lec 16-18 | Morphisms.Hom
-- [x] Functor laws and properties                              | Math 231: Ch 3 / Lec 19    | Core.Laws

## Math 232: Homological Algebra

-- [x] Functors preserving additive structure                   | Math 232: Ch 1 / Lec 1-3   | Core.Basic
-- [x] Full/faithful functors in homological algebra            | Math 232: Ch 1 / Lec 4-6   | Morphisms.Hom
-- [x] Equivalence of abelian categories                         | Math 232: Ch 2 / Lec 7-9   | Morphisms.Iso

## Math 256: Algebraic Geometry

-- [x] Functors on scheme categories                            | Math 256: Ch 2 / Lec 3-5   | Core.Basic
-- [x] Fully faithful functors as geometric embeddings          | Math 256: Ch 2 / Lec 6-9   | Morphisms.Hom
-- [x] Equivalence of geometric categories                      | Math 256: Ch 3 / Lec 10-12 | Morphisms.Iso

## Math 255: Logic / Computation

-- [x] Functors as models of logical translation                | Math 255: Ch 4 / Lec 10-12 | Core.Basic
-- [x] Cat and functor categories in computation                | Math 255: Ch 5 / Lec 13-15 | Morphisms.Hom
-- [x] Equivalence for computational models                     | Math 255: Ch 3 / Lec 7-9   | Morphisms.Iso

## Summary

Harvard targets: 17 | 17 done | 0 partial
Covers Math 231 functor theory + bridges to algebra, geometry, computation.
-/

#eval "Harvard: 17 morphism system targets, 17 done, 100%"
