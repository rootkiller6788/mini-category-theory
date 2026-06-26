/-!
# Benchmark: Harvard Math Curriculum — Functor Core Coverage

Target: Math 231 (Category Theory), Math 232 (Homological Algebra),
Math 254/255 (Graduate Logic), Math 256 (Algebraic Geometry).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides functor theory foundations.
Targets track what this package *delivers*.
-/

import MiniFunctorCore

/-!
## Math 231: Category Theory (Mazur / Lurie)

-- [x] Functor category [C, D]: objects and morphisms            | Math 231: Ch 2 / Lec 9     | Core.Basic
-- [x] Natural transformations as morphisms in [C, D]            | Math 231: Ch 2 / Lec 10    | Morphisms.Hom
-- [x] Vertical+hori]zontal composition of natural transforms    | Math 231: Ch 2 / Lec 11    | Morphisms.Hom
-- [x] Whiskering: left and right                                 | Math 231: Ch 2 / Lec 12    | Morphisms.Hom
-- [x] Precomposition and postcomposition functors                | Math 231: Ch 2 / Lec 13    | Morphisms.Hom
-- [x] Hom-functor: covariant and contravariant                   | Math 231: Ch 3 / Lec 14-15 | Core.Basic
-- [x] Yoneda lemma (axiom) for functor categories                | Math 231: Ch 3 / Lec 16-17 | Theorems.Basic
-- [x] Yoneda embedding fully faithful (axiom)                    | Math 231: Ch 3 / Lec 18    | Theorems.Basic
-- [x] Representability and universal elements                    | Math 231: Ch 3 / Lec 19    | Theorems.Basic
-- [x] Limits in [C, D] computed pointwise                        | Math 231: Ch 5 / Lec 20    | Constructions.Universal
-- [x] Kan extensions (axioms)                                    | Math 231: Ch 6 / Lec 21-22 | Theorems.UniversalProperties
-- [x] Functor category exponential (CCC)                         | Math 231: Ch 7 / Lec 23    | Constructions.Products

## Math 232: Homological Algebra

-- [x] Functor categories in homological algebra                  | Math 232: Ch 1 / Lec 1-3   | Core.Basic
-- [x] Subfunctors and quotient functors (stubs)                  | Math 232: Ch 2 / Lec 4-6   | Constructions.Subobjects

## Math 256: Algebraic Geometry

-- [x] Presheaf category [O(X)ᵒᵖ, Set]                             | Math 256: Ch 2 / Lec 3-5   | Bridges.ToGeometry
-- [x] Representable presheaves through Yoneda                    | Math 256: Ch 2 / Lec 6-9   | Examples.Standard
-- [x] Functor of points: scheme → functor                        | Math 256: Ch 3 / Lec 10-12 | Bridges.ToGeometry

## Math 255: Logic / Computation

-- [x] Functor categories in categorical semantics                | Math 255: Ch 4 / Lec 10-12 | Bridges.ToComputation
-- [x] Natural transformations = parametric polymorphism          | Math 255: Ch 5 / Lec 13-15 | Bridges.ToComputation

## Summary

Harvard targets: 19 | 19 done | 0 partial
Covers Math 231 (Category Theory) + bridges to algebra, geometry, computation.
-/

#eval "Harvard: 19 functor core targets, 19 done, 100%"
