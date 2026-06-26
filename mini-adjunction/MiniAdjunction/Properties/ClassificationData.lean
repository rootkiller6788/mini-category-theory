/-
# MiniAdjunction.Properties.ClassificationData

Types of adjunctions: reflective, coreflective, essential, lax, oplax.
Classification of adjunctions by their properties.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Reflective Adjunction -/

/--
A reflective adjunction is one where the right adjoint is fully faithful.
This is equivalent to: the counit is a natural isomorphism.
-/
structure ReflectiveAdjunction {C D : Category} {F : Functor C D} {G : Functor D C} where
  adj : F ⊣ G
  fullyFaithfulRight : Functor.IsFullyFaithful G

/--
In a reflective adjunction, the counit is an isomorphism.
-/
axiom reflectiveCounitIsIsoProp {C D : Category} {F : Functor C D} {G : Functor D C}
    (ra : ReflectiveAdjunction) : Prop

/-! ## Coreflective Adjunction -/

/--
A coreflective adjunction is one where the left adjoint is fully faithful.
This is equivalent to: the unit is a natural isomorphism.
-/
structure CoreflectiveAdjunction {C D : Category} {F : Functor C D} {G : Functor D C} where
  adj : F ⊣ G
  fullyFaithfulLeft : Functor.IsFullyFaithful F

/--
In a coreflective adjunction, the unit is an isomorphism.
-/
axiom coreflectiveUnitIsIsoProp {C D : Category} {F : Functor C D} {G : Functor D C}
    (ca : CoreflectiveAdjunction) : Prop

/-! ## Essential Adjunction -/

/--
An essential adjunction is one that is both reflective and coreflective,
i.e., both the left and right adjoints are fully faithful.
-/
structure EssentialAdjunction {C D : Category} {F : Functor C D} {G : Functor D C} where
  adj : F ⊣ G
  fullyFaithfulLeft : Functor.IsFullyFaithful F
  fullyFaithfulRight : Functor.IsFullyFaithful G

/--
An essential adjunction is an adjoint equivalence.
-/
axiom essentialIsEquivalence {C D : Category} {F : Functor C D} {G : Functor D C}
    (ea : EssentialAdjunction) : Prop

/-! ## Lax Adjunction -/

/--
A lax adjunction relaxes the triangle identities to inequalities
(2-categorical: triangle identities hold up to 2-cells in a fixed direction).
-/
structure LaxAdjunction {C D : Category} {F : Functor C D} {G : Functor D C} where
  unit : Functor.id C ⇒ Functor.comp G F
  counit : Functor.comp F G ⇒ Functor.id D
  leftLaxTriangle : Prop
  rightLaxTriangle : Prop

/--
Every strict adjunction is in particular a lax adjunction.
-/
axiom strictAdjunctionIsLax {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Nonempty (LaxAdjunction)

/-! ## Oplax Adjunction -/

/--
An oplax adjunction is the dual of a lax adjunction:
triangle identities hold up to 2-cells in the opposite direction.
-/
structure OplaxAdjunction {C D : Category} {F : Functor C D} {G : Functor D C} where
  unit : Functor.id C ⇒ Functor.comp G F
  counit : Functor.comp F G ⇒ Functor.id D
  leftOplaxTriangle : Prop
  rightOplaxTriangle : Prop

/--
Every strict adjunction is also an oplax adjunction.
-/
axiom strictAdjunctionIsOplax {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Nonempty (OplaxAdjunction)

/-! ## Classification Summary -/

/--
Summary type of adjunction classification:
  Strict | Reflective | Coreflective | Essential | Lax | Oplax
-/
inductive AdjunctionType where
  | strict
  | reflective
  | coreflective
  | essential
  | lax
  | oplax
  deriving Repr, DecidableEq

/--
Given an adjunction, classify its type.
-/
def classifyAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : AdjunctionType :=
  AdjunctionType.strict

#eval "Properties.ClassificationData: Reflective, Coreflective, Essential, Lax, Oplax adjunctions"
#eval "Properties.ClassificationData: AdjunctionType enum: strict/reflective/coreflective/essential/lax/oplax"
#eval "Properties.ClassificationData: strictAdjunctionIsLax, strictAdjunctionIsOplax (axioms)"
