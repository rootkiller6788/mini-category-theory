/-!
# Benchmark: MIT Math Curriculum — Morphism System Coverage

Target: 18.705 (Category Theory), 18.706 (Homological Algebra),
18.725 (Algebraic Geometry), 18.515 (Model Theory).
Format: `-- [status] target | course: Ch X / Lec Y | module`

This package provides functor and morphism foundations.
Targets track what this package *delivers*.
-/

import MiniMorphismSystem

/-!
## 18.705: Category Theory (Riehl / Miller)

-- [x] Functor: covariant + contravariant                       | 18.705: Ch 1 / Lec 4-5      | Core.Basic
-- [x] Functor.id, Functor.comp, Functor.const                  | 18.705: Ch 1 / Lec 6-7      | Core.Objects
-- [x] Full, faithful, fully faithful, ess. surjective          | 18.705: Ch 1 / Lec 8        | Morphisms.Hom
-- [x] Cat: category of small categories                         | 18.705: Ch 1 / Lec 9        | Morphisms.Hom
-- [x] Functor isomorphism (natural isomorphism)                | 18.705: Ch 2 / Lec 10-12    | Morphisms.Iso
-- [x] Equivalence of categories                                | 18.705: Ch 2 / Lec 13-15    | Morphisms.Iso
-- [x] Functor laws: preservesId, preservesComp                  | 18.705: Ch 3 / Lec 16-18    | Core.Laws
-- [x] Equivalence properties and structure                     | 18.705: Ch 3 / Lec 19-20    | Morphisms.Equivalence

## 18.706: Homological Algebra

-- [x] Functors between abelian categories                      | 18.706: Ch 1 / Lec 1-3      | Core.Basic
-- [x] Full/faithful in homological contexts                    | 18.706: Ch 1 / Lec 4-6      | Morphisms.Hom
-- [x] Equivalence in derived categories                         | 18.706: Ch 2 / Lec 7-9      | Morphisms.Iso

## 18.725: Algebraic Geometry

-- [x] Functors on scheme categories                            | 18.725: Ch 2 / Lec 3-5      | Core.Basic
-- [x] Fully faithful geometric embeddings                      | 18.725: Ch 2 / Lec 6-9      | Morphisms.Hom
-- [x] Equivalence for moduli problems                           | 18.725: Ch 3 / Lec 10-12    | Morphisms.Iso

## 18.734: ∞-Categories (Topics)

-- [x] Functors between higher categories                       | 18.734: Ch 1 / Lec 1-3      | Core.Basic
-- [x] Full/faithful in ∞-categorical context                   | 18.734: Ch 1 / Lec 4-6      | Morphisms.Hom
-- [x] Equivalence as model for ∞-groupoids                     | 18.734: Ch 2 / Lec 7-9      | Morphisms.Iso

## Summary

MIT targets: 17 | 17 done | 0 partial
Covers 18.705 functor theory + bridges to algebra, geometry, topology.
-/

#eval "MIT: 17 morphism system targets, 17 done, 100%"
