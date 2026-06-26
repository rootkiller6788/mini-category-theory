import MiniAdjunction

open MiniAdjunction
open MiniCategoryCore
open MiniMorphismSystem

-- Check all definitions are accessible
#check Adjunction
#check FreeForgetful
#check HomAdjunction
#check HomAdjunction.toUnit
#check HomAdjunction.toCounit
#check Adjunction.toHomAdjunction
#check IsLeftAdjoint
#check IsRightAdjoint
#check HasLeftAdjoint
#check HasRightAdjoint
#check identityAdjunction

-- Core/Laws
#check unit_naturality
#check counit_naturality
#check leftTriangleEq
#check rightTriangleEq
#check adjunctionHomBijection
#check adjunctionHomBijectionInv
#check homBijectionIsBijection

-- Morphisms
#check AdjunctionMorphism
#check AdjunctionMorphism.id
#check AdjunctionMorphism.comp
#check EquivalentAdjunctions
#check AdjointEquivalence

-- Constructions
#check ProductExponentialAdjunction
#check setProductExponential
#check curry
#check uncurry
#check FreeMonoidAdjunction
#check ReflectiveSubcategory
#check CoreflectiveSubcategory
#check QuotientAdjunction

-- Properties
#check ReflectiveAdjunction
#check CoreflectiveAdjunction
#check EssentialAdjunction
#check LaxAdjunction
#check OplaxAdjunction
#check AdjunctionType
#check classifyAdjunction

-- Theorems
#check adjointCorrespondence
#check adjointCorrespondenceInv
#check adjointTranspose
#check adjointTransposeInv
#check unitIsTransposeOfId
#check counitIsTransposeOfId

-- Examples
#check freeMonoidForgetfulAdjunction
#check curryUncurryInverse

-- Bridges
#check GaloisConnection
#check StoneCechAdjunction
#check DiscreteTopologyAdjunction
#check SheafSpaceAdjunction
#check SpecGlobalSectionsAdjunction
#check CurryHowardAdjunction
#check MonadFromAdjunction
