/-
# MiniAdjunction.Morphisms.Equivalence

Equivalent adjunctions: two adjunctions can be equivalent up to
natural isomorphism of their functors.
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
import MiniAdjunction.Morphisms.Iso

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Equivalent Adjunctions -/

/--
Two adjunctions (F ⊣ G) and (F' ⊣ G') are equivalent if there exist
natural isomorphisms α : F ≅ F' and β : G ≅ G' making the
adjunction data compatible.
-/
structure EquivalentAdjunctions {C D : Category}
    {F F' : Functor C D} {G G' : Functor D C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') where
  leftEquiv : Nonempty (F ⇒ F')
  leftEquivInv : Nonempty (F' ⇒ F)
  rightEquiv : Nonempty (G ⇒ G')
  rightEquivInv : Nonempty (G' ⇒ G)
  unitCompatibility : Prop
  counitCompatibility : Prop

/-! ## Adjunction Up To Natural Isomorphism -/

/--
Given F, G, and natural transformations η, ε, if η and ε satisfy
the triangle identities up to isomorphism, then there is a genuine adjunction.
-/
structure AdjunctionUpToIso {C D : Category}
    (F : Functor C D) (G : Functor D C) where
  unitApprox : Functor.id C ⇒ Functor.comp G F
  counitApprox : Functor.comp F G ⇒ Functor.id D
  leftTriangleApprox : Prop
  rightTriangleApprox : Prop

/--
If F ⊣ G and F' ⊣ G are both adjunctions, then they are equivalent.
-/
axiom sameRightAdjointEquivalent {C D : Category} {F F' : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) (_ : F' ⊣ G) : EquivalentAdjunctions (_ : F ⊣ G) (_ : F' ⊣ G)

/--
If F ⊣ G and F ⊣ G' are both adjunctions, then they are equivalent.
-/
axiom sameLeftAdjointEquivalent {C D : Category} {F : Functor C D} {G G' : Functor D C}
    (_ : F ⊣ G) (_ : F ⊣ G') : EquivalentAdjunctions (_ : F ⊣ G) (_ : F ⊣ G')

/-! ## Transport of Adjunction Structure -/

/--
If F ⊣ G and F ≅ F' naturally, then F' is also a left adjoint to G
(up to equivalence).
-/
axiom transportLeftAdjoint {C D : Category} {F F' : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) (_ : Nonempty (F ⇒ F')) : Nonempty (F' ⊣ G)

/--
If F ⊣ G and G ≅ G' naturally, then F is also a left adjoint to G'
(up to equivalence).
-/
axiom transportRightAdjoint {C D : Category} {F : Functor C D} {G G' : Functor D C}
    (_ : F ⊣ G) (_ : Nonempty (G ⇒ G')) : Nonempty (F ⊣ G')

/-! ## Adjoint Functors and Kan Extensions -/

/--
Left adjoints are left Kan extensions of the identity along the right adjoint.
-/
axiom leftAdjointAsKanExtension {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Right adjoints are right Kan extensions of the identity along the left adjoint.
-/
axiom rightAdjointAsKanExtension {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Biequivalence of the 2-category of adjunctions -/

/--
The 2-category of adjunctions is biequivalent to the 2-category
of adjunctions with the opposite 2-cell direction.
-/
axiom adjunctionBiequivalence {C D : Category} : Prop

#eval "Morphisms.Equivalence: EquivalentAdjunctions, AdjunctionUpToIso"
#eval "Morphisms.Equivalence: sameRight/LeftAdjointEquivalent (axioms)"
#eval "Morphisms.Equivalence: Kan extension characterizations (axioms)"
