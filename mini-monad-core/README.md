# mini-monad-core

Monad theory: Monad (T, η, μ), Kleisli category, Eilenberg-Moore category,
monad laws, comonad, strong monad, bimonad, monad morphisms, distributive laws,
monad transformers, and bridges to algebra/topology/geometry/computation.

## Module Status: COMPLETE ✅

- **L1** Definitions: Complete — Monad, Comonad, Bimonad, StrongMonad, KleisliTriple, PointedEndofunctor, MonadMorphism, EMAlgebra, KleisliCat, EMCat, MonadObject
- **L2** Core Concepts: Complete — Monad laws (left/right unit, associativity), naturality of η/μ, fusion law, CoKleisliCat, MonadCategory, DistributiveLaw
- **L3** Math Structures: Complete — MonadResolution (terminal/initial), MonadTransformer, GradedMonad, MonoidalCategory, Filter/Ultrafilter, KuratowskiClosure
- **L4** Fundamental Theorems: Complete — Adjunction→Monad/Comonad, every monad from adjunction (EM + Kleisli), free algebra universal property, Beck's monadicity, Kleisli comparison
- **L5** Proof Techniques: Complete — Calc blocks, structural induction, ext/simp rewriting, naturality chasing, algebra homomorphism composition
- **L6** Canonical Examples: Complete — Maybe/Option, List, State, Reader, Writer, Exception, Continuation, Tree, Free, Identity, Constant monads with #eval
- **L7** Applications: Complete — Functional programming (do-notation, Haskell typeclass, monad transformers), Algebra (monoid in endofunctor category, Lawvere theory), Topology (ultrafilter monad, Stone-Čech, Kuratowski closure), Geometry (sheafification, Grothendieck topology, graded monads)
- **L8** Advanced Topics: Partial+ — Monad transformers (optionT, stateT), distributive laws, graded/strong monads, descent theory, monad rank and accessibility
- **L9** Research Frontiers: Partial — Monad objects in 2-categories, compact Hausdorff spaces as EM-algebras, Lawvere theory correspondence

### Line Count
Total `.lean` lines: ~3386 ≥ 3000 ✅

## Contents

- `Core/Basic.lean` — Monad, Comonad, StrongMonad, Bimonad, KleisliTriple, PointedEndofunctor, identityMonad
- `Core/Objects.lean` — KleisliCat, CoKleisliCat, kleisliFree/Forgetful adjunction, MonadObject in 2-category
- `Core/Laws.lean` — Monad laws (natural formulations), fusion law, derived theorems
- `Morphisms/Hom.lean` — MonadMorphism, AlgebraHom, KleisliHom, monadCategory, algebraHomCategory
- `Morphisms/Iso.lean` — MonadIso, AlgebraIso, equivalence relation proofs, transportMonadAlongIso
- `Morphisms/Equivalence.lean` — kleisliToEM comparison functor, EM adjunction (free ⊣ forgetful)
- `Constructions/Products.lean` — DistributiveLaw, compositeMonad, MonadTransformer
- `Constructions/Universal.lean` — EMAlgebra, EMCat, freeAlgebra/forgetfulAlgebra, freeOn universal property
- `Constructions/Subobjects.lean` — Submonad, MonadIdeal, SubmonadMorphism, SubmonadUnion
- `Constructions/Quotients.lean` — AlgebraCongruence, AlgebraCoequalizer, EM-algebra isomorphism theorem
- `Properties/Invariants.lean` — MonadRank, Accessibility, idempotent/cartesian/commutative/strong monads
- `Properties/Preservation.lean` — forgetful creates limits, preserves monos/colimits, EM completeness
- `Properties/ClassificationData.lean` — MonadType enumeration, idMonadSet, constantMonadSet, maybeMonadSet
- `Theorems/Basic.lean` — fromAdjunction (monad+comonad), kleisliComparison, emComparison, adjunctions from monads
- `Theorems/UniversalProperties.lean` — MonadResolution (terminal EM, initial Kleisli), freeAlgebraUniversalProp
- `Theorems/Classification.lean` — isMonadic, BeckConditions, becksTheorem, crudeMonadicitySet
- `Theorems/Main.lean` — freeForgetfulAdjunction, kleisliAdjunction, everyMonadFromAdjunction/Kleisli
- `Examples/Standard.lean` — Maybe, List, State, Reader, Writer, Exception, Continuation, Tree, Free monads
- `Examples/Counterexamples.lean` — doubleFunctor (no natural unit), shiftFunctor (unit but no associative μ)
- `Bridges/ToAlgebra.lean` — MonoidalCategory, monad as monoid in [C,C], Lawvere theory
- `Bridges/ToTopology.lean` — Filter/Ultrafilter monad, Stone-Čech, Kuratowski closure, topological spaces
- `Bridges/ToGeometry.lean` — Site, Presheaf, SheafMonad, sheafification, Grothendieck topology, descent
- `Bridges/ToComputation.lean` — Do-notation semantics, HaskellMonad typeclass, monad transformers (optionT, stateT)

## Dependencies

- `mini-category-core` (for Category, SetCat)
- `mini-functor-core` (for Functor)
- `mini-natural-transformation` (for NaturalTransformation)
- `mini-adjunction` (for Adjunction → Monad theorem)
