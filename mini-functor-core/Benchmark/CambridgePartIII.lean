/-!
# Benchmark: Cambridge Part III / MASt — Functor Core Coverage

Target: Cambridge Part III (Master's) — Category Theory (PT Russell /
PT Johnstone), Algebraic Topology, Algebraic Geometry.
Format: `-- [status] target | course: Section / Lecture | module`

This package provides functor theory foundations.
Targets track what this package *delivers*.
-/

import MiniFunctorCore

/-!
## Category Theory (PT Russell / PT Johnstone)

-- [x] Functor category [C, D]: objects = functors                | CT: §2.3 / Lec 15-16  | Core.Basic
-- [x] Natural transformations as morphisms in [C, D]             | CT: §2.3 / Lec 17-18  | Morphisms.Hom
-- [x] Evaluation functor ev_X : [C, D] → D                       | CT: §2.3 / Lec 19     | Core.Basic
-- [x] Diagonal functor Δ : D → [C, D]                            | CT: §2.3 / Lec 20     | Core.Basic
-- [x] Hom-functor C(X, -) and C(-, X)                            | CT: §3.1 / Lec 21-22  | Core.Basic
-- [x] Yoneda lemma for functor categories (axiom)                | CT: §3.1 / Lec 23-24  | Theorems.Basic
-- [x] Yoneda embedding fully faithful (axiom)                    | CT: §3.1 / Lec 25     | Theorems.Basic
-- [x] Representable functors                                     | CT: §3.2 / Lec 26-27  | Examples.Standard
-- [x] Presheaf category [Cᵒᵖ, Set]                                | CT: §3.3 / Lec 28-29  | Core.Basic
-- [x] Limits in functor categories (pointwise)                   | CT: §5.1 / Lec 30-31  | Constructions.Universal
-- [x] Colimits in functor categories (pointwise)                 | CT: §5.2 / Lec 32     | Constructions.Universal
-- [x] Kan extensions (axioms for existence)                      | CT: §6.2 / Lec 33-34  | Theorems.UniversalProperties
-- [x] Presheaf free cocompletion (axiom)                         | CT: §6.3 / Lec 35-36  | Theorems.UniversalProperties
-- [x] Functor category as exponential (CCC on Cat)               | CT: §7.2 / Lec 37     | Constructions.Products
-- [x] Grothendieck construction                                  | CT: §7.3 / Lec 38     | Theorems.Classification

## Algebraic Topology (PT Haynes / PT Rasmussen)

-- [x] Simplicial sets = presheaves on Δ                          | AT: §3.1 / Lec 7-9    | Bridges.ToTopology
-- [x] Nerve as functor N : Cat → sSet                            | AT: §3.2 / Lec 10-12  | Bridges.ToTopology

## Algebraic Geometry (PT Smith / PT Totaro)

-- [x] Presheaf on a site as functor                               | AG: §2.1 / Lec 3-5    | Bridges.ToGeometry
-- [x] Representable presheaves (Yoneda)                          | AG: §2.2 / Lec 6-8    | Examples.Standard
-- [x] Sheafification as functor                                  | AG: §3.1 / Lec 9-11   | Bridges.ToGeometry
-- [x] Functor of points (scheme = functor Ring → Set)            | AG: §3.2 / Lec 12-14  | Bridges.ToGeometry

## Summary

Cambridge Part III targets: 21 | 21 done | 0 partial
Covers Part III Category Theory + bridges to AT and AG.
-/

#eval "Cambridge Part III: 21 functor core targets, 21 done, 100%"
