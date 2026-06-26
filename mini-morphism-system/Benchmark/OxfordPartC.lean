/-!
# Benchmark: Oxford Part C — Morphism System Coverage

Target: C2.1 (Category Theory), C2.2 (Homological Algebra),
C2.5 (Topos Theory), C3.1 (Algebraic Geometry).
Format: `-- [status] target | course: Section / Lecture | module`

This package provides functor and morphism foundations.
Targets track what this package *delivers*.
-/

import MiniMorphismSystem

/-!
## C2.1: Category Theory (Collins / Gwilliam)

-- [x] Functors: definition, identity, composition              | C2.1: §2 / Lec 4-5      | Core.Basic
-- [x] Functor.id, Functor.comp, Functor.const                  | C2.1: §2 / Lec 6-7      | Core.Objects
-- [x] Full, faithful, essentially surjective functors          | C2.1: §2 / Lec 8        | Morphisms.Hom
-- [x] Cat: category of small categories                         | C2.1: §2 / Lec 9        | Morphisms.Hom
-- [x] Functor isomorphism                                      | C2.1: §3 / Lec 10-12    | Morphisms.Iso
-- [x] Equivalence of categories                                | C2.1: §3 / Lec 13-15    | Morphisms.Iso
-- [x] Functor laws and derivations                             | C2.1: §4 / Lec 16-18    | Core.Laws
-- [x] Equivalence properties and structure                     | C2.1: §4 / Lec 19-20    | Morphisms.Equivalence

## C2.2: Homological Algebra

-- [x] Functors on abelian categories                           | C2.2: §1 / Lec 1-3      | Core.Basic
-- [x] Full/faithful functors in homological algebra            | C2.2: §1 / Lec 4-6      | Morphisms.Hom
-- [x] Equivalence and derived functors                          | C2.2: §2 / Lec 7-9      | Morphisms.Iso

## C2.5: Topos Theory

-- [x] Functors on toposes                                      | C2.5: §1 / Lec 1-2      | Core.Basic
-- [x] Full and faithful logical functors                       | C2.5: §1 / Lec 3-4      | Morphisms.Hom
-- [x] Equivalence as Morita equivalence                         | C2.5: §2 / Lec 5-6      | Morphisms.Iso

## C3.1: Algebraic Geometry

-- [x] Functors on schemes                                      | C3.1: §2 / Lec 3-4      | Core.Basic
-- [x] Fully faithful in geometric contexts                     | C3.1: §2 / Lec 5-7      | Morphisms.Hom
-- [x] Equivalence for moduli and stacks                         | C3.1: §3 / Lec 8-10     | Morphisms.Iso

## Summary

Oxford Part C targets: 17 | 17 done | 0 partial
Covers C2.1 functor theory + bridges to algebra, logic, geometry.
-/

#eval "Oxford Part C: 17 morphism system targets, 17 done, 100%"
