import MiniMonadCore

-- Type-check all definitions to ensure no regressions
open MiniMonadCore
open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

-- Core
#check Monad
#check MonadMorphism
#check KleisliCat
#check monadLeftUnitLaw
#check monadRightUnitLaw
#check monadAssociativityLaw
#check monadLawsHold
#check EMAlgebra
#check EMCat
#check fromAdjunction

-- Core/Objects
#check KleisliCat

-- Core/Laws
#check monadLawsHold

-- Morphisms/Hom
#check preservesUnit
#check preservesMultiplication
#check monadMorphismLaws
#check AlgebraHom
#check algebraHomId
#check algebraHomComp
#check KleisliHom
#check kleisliId
#check kleisliComp
#check kleisliCompAssoc

-- Morphisms/Iso
#check MonadIso
#check monadIsoRefl
#check monadIsoSymm
#check AlgebraIso
#check areEquivalentMonads
#check equivalentMonadsRefl
#check equivalentMonadsSymm

-- Morphisms/Equivalence
#check kleisliToEM
#check emForgetful
#check emFree
#check emAdjunction

-- Constructions/Subobjects
#check Submonad
#check QuotientMonad
#check MonadIdeal
#check trivialSubmonad
#check unitSubmonad

-- Constructions/Quotients
#check AlgebraCongruence
#check AlgebraQuotient
#check AlgebraCoequalizer
#check FreeAlgebraQuotient

-- Constructions/Products
#check DistributiveLaw
#check compositeMonad
#check MonadTransformer
#check identityTransformer

-- Constructions/Universal
#check freeAlgebra
#check forgetfulAlgebra
#check freeOn
#check freeOnUniversal

-- Properties/Invariants
#check MonadRank
#check Accessibility
#check FinitaryMonad
#check isFinitary
#check RankedMonad
#check noRankMonad
#check isIdempotent
#check isStrictIdempotent
#check isCartesian

-- Properties/Preservation
#check forgetfulCreatesLimits
#check kleisliPreservesColimits
#check forgetfulReflectsIsos
#check preservesFilteredColimits
#check triviallyPreservesFiltered
#check LiftingResult
#check hasAlgebraLifting

-- Properties/ClassificationData
#check MonadType
#check idMonadSet
#check constantMonadSet
#check maybeMonadSet

-- Theorems/UniversalProperties
#check MonadResolution
#check terminalResolution
#check kleisliResolution
#check freeAlgebraUniversalProp
#check emCatCreatesLimitsStatement

-- Theorems/Classification
#check isMonadic
#check isComonadic
#check BeckConditions
#check becksTheorem
#check DistLawType
#check ClassifiedDistLaw
#check classifyDistLaw
#check classifyMonad

-- Theorems/Main
#check freeForgetfulAdjunction
#check kleisliFreeFunctor
#check kleisliForgetfulFunctor
#check kleisliAdjunction
#check everyMonadFromAdjunction
#check everyMonadFromKleisli
#check comparisonEMtoKleisli
#check comparisonFullAndFaithful
#check freeForgetfulRecovers

-- Examples/Standard
#check maybeMonad
#check listMonad
#check stateMonad
#check powersetFunctor

-- Examples/Counterexamples
#check doubleFunctor
#check noUnitForDouble
#check shiftFunctor
#check shiftHasUnit
#check freeVecFunc
#check forgetVecFunc
#check nonIsoComparison

-- Bridges/ToAlgebra
#check MonoidalCategory
#check MonoidIn
#check endofunctorMonoidal
#check monadAsMonoid
#check monoidToMonad
#check OperadicMonad

-- Bridges/ToTopology
#check Filter
#check Ultrafilter
#check ultrafilterFunctor
#check UltrafilterMonad
#check ultrafilterMonadSketch
#check StoneCechCompactification
#check stoneCechMonadAlgebra

-- Bridges/ToGeometry
#check Site
#check Presheaf
#check presheafCategory
#check SheafMonad
#check sheafificationMonad
#check GradedMonoid
#check GradedMonad
#check trivialGradedMonad
#check TangentBundle
#check tangentMonadConcept

-- Bridges/ToComputation
#check Maybe
#check Maybe.map
#check Maybe.join
#check ioMonadConcept
#check doUnitSyntax
#check doBindSyntax
#check IOConcept
