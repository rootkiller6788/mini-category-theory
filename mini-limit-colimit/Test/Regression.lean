import MiniLimitColimit

open MiniLimitColimit

-- Check all core definitions exist and typecheck
#check Diagram
#check Cone
#check Cocone
#check ConeCat
#check Limit
#check Colimit
#check IsLimit
#check IsColimit
#check limitUnique
#check colimitUnique
#check limitFromIsLimit
#check conePrecompose
#check ConeMorphism
#check CoconeMorphism
#check ConeIso
#check CoconeIso
#check PreservesLimit
#check PreservesColimit
#check functorOnCone
#check functorOnCocone
#check LimitUniversalEquivalence

#check IsProduct
#check IsCoproduct
#check productDiagram
#check productOfPairInSet
#check coproductOfPairInSet
#check Fork
#check Equalizer
#check equalizerInSet
#check PullbackCone
#check Pullback
#check pullbackInSet
#check Cofork
#check Coequalizer
#check coequalizerInSet
#check PushoutCocone
#check Pushout

#check IsComplete
#check IsCocomplete
#check IsFinitelyComplete
#check IsFinitelyCocomplete
#check limitFromProductsAndEqualizersSetCat

#check isMonic
#check isEpic
#check Continuous
#check Cocontinuous
#check CreatesLimitsOfShape
#check ReflectsLimitsOfShape

#check IsFiniteCategory
#check IsFiltered
#check IsDirected
#check LimitType
#check ColimitType

#check limitUniversal
#check colimitUniversal
#check parametrizedLimitUniversal

#check classifyLimit
#check classifyColimit
#check setCatComplete
#check setCatCocomplete

#check Group
#check AbGroup
#check Ring
#check Grp
#check Ab
#check RingCat

#check TopSpace
#check Top

#check tupleAsProduct
#check sumAsCoproduct

#check setProductUnitBool
#check setCoproductUnitBool
#check setEqualizerExample
#check setPullbackExample
