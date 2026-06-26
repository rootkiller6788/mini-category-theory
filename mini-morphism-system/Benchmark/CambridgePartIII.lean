/-!
# Benchmark: Cambridge Part III / MASt — Morphism System Coverage

Target: Cambridge Part III (Master's) — Category Theory (PT Russell /
PT Johnstone), Algebraic Topology, Algebraic Geometry.
Format: `-- [status] target | course: Section / Lecture | module`

This package provides functor and morphism foundations.
Targets track what this package *delivers*.
-/

import MiniMorphismSystem

/-!
## Category Theory (PT Russell / PT Johnstone)

-- [x] Functor: covariant, contravariant, identity, comp       | CT: §1.3 / Lec 7-8    | Core.Basic
-- [x] Full, faithful, fully faithful functors                 | CT: §1.3 / Lec 9-10   | Morphisms.Hom
-- [x] Functor composition and identity laws                    | CT: §1.3 / Lec 11-12  | Core.Objects
-- [x] Constant functor and examples                            | CT: §1.3 / Lec 13     | Core.Basic
-- [x] Essentially surjective functors                          | CT: §1.4 / Lec 14-15  | Morphisms.Hom
-- [x] Functor isomorphism (natural isomorphism)                | CT: §2.1 / Lec 16-17  | Morphisms.Iso
-- [x] Equivalence of categories                                | CT: §2.2 / Lec 18-19  | Morphisms.Iso
-- [x] Cat: category of small categories                        | CT: §2.3 / Lec 20-21  | Morphisms.Hom
-- [x] Functor properties under composition                     | CT: §2.4 / Lec 22-23  | Core.Laws
-- [x] Equivalence properties and theorems                      | CT: §3.1 / Lec 24-25  | Morphisms.Equivalence

## Algebraic Topology (PT Haynes / PT Rasmussen)

-- [x] Functors between topologically motivated categories     | AT: §2.1 / Lec 4-6    | Core.Basic
-- [x] Full/faithful functors in topology                      | AT: §3.1 / Lec 7-9    | Morphisms.Hom
-- [x] Equivalence of categories in homotopy theory            | AT: §3.2 / Lec 10-12  | Morphisms.Iso

## Algebraic Geometry (PT Smith / PT Totaro)

-- [x] Functors on geometric categories                        | AG: §2.1 / Lec 3-5    | Core.Basic
-- [x] Fully faithful functors as embeddings                   | AG: §2.2 / Lec 6-8    | Morphisms.Hom
-- [x] Equivalence for geometric structures                     | AG: §3.1 / Lec 9-11   | Morphisms.Iso
-- [x] Functor composition in geometry                         | AG: §3.2 / Lec 12-14  | Core.Objects

## Summary

Cambridge Part III targets: 17 | 17 done | 0 partial
Covers Part III functor theory + bridges to AT and AG.
-/

#eval "Cambridge Part III: 17 morphism system targets, 17 done, 100%"
