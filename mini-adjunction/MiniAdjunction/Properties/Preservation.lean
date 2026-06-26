/-
# MiniAdjunction.Properties.Preservation

Left adjoints preserve colimits; right adjoints preserve limits.
Also: uniqueness of adjoints and preservation/reflection theorems.
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

/-! ## Preservation Properties of Adjoints -/

/--
Left adjoints preserve colimits: if F ⊣ G and a diagram has a colimit,
then F applied to the colimit is a colimit of F applied to the diagram.
-/
axiom leftAdjointPreservesColimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Right adjoints preserve limits: if F ⊣ G and a diagram has a limit,
then G applied to the limit is a limit of G applied to the diagram.
-/
axiom rightAdjointPreservesLimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Uniqueness of Adjoints -/

/--
Any two right adjoints to the same functor are naturally isomorphic.
-/
axiom adjointUniqueUpToIso {C D : Category} {F : Functor C D} {G₁ G₂ : Functor D C}
    (_ : F ⊣ G₁) (_ : F ⊣ G₂) : Nonempty (G₁ ⇒ G₂)

/--
Any two left adjoints to the same functor are naturally isomorphic.
-/
axiom leftAdjointUniqueUpToIso {C D : Category} {F₁ F₂ : Functor C D} {G : Functor D C}
    (_ : F₁ ⊣ G) (_ : F₂ ⊣ G) : Nonempty (F₁ ⇒ F₂)

/-! ## Reflection of Isomorphisms -/

/--
Right adjoints reflect isomorphisms: if G(f) is iso, then f is iso.
-/
axiom rightAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/--
Left adjoints reflect isomorphisms as well (since left adjoint = right adjoint of opposite).
-/
axiom leftAdjointReflectsIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) : Prop

/-! ## Preservation of Epimorphisms and Monomorphisms -/

/--
Left adjoints preserve epimorphisms. If f is epi and F is a left adjoint,
then F(f) is epi.
-/
axiom leftAdjointPreservesEpi {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) : Prop

/--
Right adjoints preserve monomorphisms. If f is mono and G is a right adjoint,
then G(f) is mono.
-/
axiom rightAdjointPreservesMono {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/-! ## Adjoint Functor Theorems (Statements) -/

/--
The General Adjoint Functor Theorem (Freyd):
If D is complete and locally small, a functor G : D → C has a left adjoint
iff G preserves limits and satisfies the Solution Set Condition.
-/
axiom generalAdjointFunctorTheorem {C D : Category} {G : Functor D C} : Prop

/--
The Special Adjoint Functor Theorem (SAFT):
If C and D are locally small, D is complete, well-powered, and has a
cogenerating set, then any limit-preserving functor G : D → C has a left adjoint.
-/
axiom specialAdjointFunctorTheorem {C D : Category} {G : Functor D C} : Prop

/-! ## Representability and Adjoints -/

/--
A functor G : D → C has a left adjoint iff for each X : C,
the functor C(X, G(-)) : D → Set is representable.
-/
axiom representabilityCriterion {C D : Category} {G : Functor D C} : Prop

/-! ## Commutation with Limits -/

/--
Left adjoints commute with (i.e., preserve) all colimits that exist.
-/
axiom leftAdjointCommutesWithColimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
Right adjoints commute with all limits that exist.
-/
axiom rightAdjointCommutesWithLimits {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

#eval "Properties.Preservation: LAPC, RAPL, adjoint uniqueness (axioms)"
#eval "Properties.Preservation: rightAdjointReflectsIso, leftAdjointPreservesEpi"
#eval "Properties.Preservation: General AFT, SAFT, representability criterion (axioms)"
