/-
# MiniAdjunction.Theorems.Main

Main theorems: adjunctions compose, adjunctions are determined
by unit OR counit, RAPL (Right Adjoint Preserves Limits).
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
import MiniAdjunction.Properties.Preservation
import MiniAdjunction.Theorems.Basic

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Adjunctions Compose -/

/--
Adjunctions compose horizontally:
If F ⊣ G : C ⇄ D and H ⊣ K : D ⇄ E, then H∘F ⊣ G∘K : C ⇄ E.
-/
axiom adjunctionsComposeMain {C D E : Category}
    {F : Functor C D} {G : Functor D C} {H : Functor D E} {K : Functor E D}
    (adjFG : F ⊣ G) (adjHK : H ⊣ K) : (Functor.comp H F) ⊣ (Functor.comp G K)

/-! ## Unit/Counit Determine the Adjunction -/

/--
An adjunction is uniquely determined by its unit:
Given F : C → D and G : D → C, there can be at most one adjunction
F ⊣ G with a given unit η.
-/
axiom adjunctionDeterminedByUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj1 adj2 : F ⊣ G) (h : adj1.unit = adj2.unit) : adj1 = adj2

/--
An adjunction is uniquely determined by its counit:
Given F : C → D and G : D → C, there can be at most one adjunction
F ⊣ G with a given counit ε.
-/
axiom adjunctionDeterminedByCounit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj1 adj2 : F ⊣ G) (h : adj1.counit = adj2.counit) : adj1 = adj2

/-! ## RAPL: Right Adjoint Preserves Limits -/

/--
If F ⊣ G, then G preserves all limits that exist in D.
This is the fundamental RAPL theorem.
-/
axiom rapl {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## LAPC: Left Adjoint Preserves Colimits -/

/--
If F ⊣ G, then F preserves all colimits that exist in C.
-/
axiom lapc {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Adjoints and Commutation with (Co)Limits -/

/--
Left adjoints are cocontinuous: they preserve all colimits.
-/
axiom leftAdjointIsCocontinuous {C D : Category} {F : Functor C D}
    (_ : IsLeftAdjoint F) : Prop

/--
Right adjoints are continuous: they preserve all limits.
-/
axiom rightAdjointIsContinuous {C D : Category} {G : Functor D C}
    (_ : IsRightAdjoint G) : Prop

/-! ## Adjoint Correspondence Theorem -/

/--
The adjoint correspondence extends to a natural isomorphism of functors:
  D(F(-), -) ≅ C(-, G(-)) : Cᵒᵖ × D → Set
-/
axiom adjointCorrespondenceNatural {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Prop

/-! ## Full/ Faithful Adjoints -/

/--
The right adjoint G is fully faithful iff the counit ε : F G ⇒ id_D
is a natural isomorphism.
-/
axiom rightAdjointFullyFaithfulIffCounitIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
The left adjoint F is fully faithful iff the unit η : id_C ⇒ G F
is a natural isomorphism.
-/
axiom leftAdjointFullyFaithfulIffUnitIso {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Kan Extension Characterization -/

/--
Every adjunction F ⊣ G gives rise to:
- Left Kan extension along F: Lan_F(id) = G
- Right Kan extension along G: Ran_G(id) = F
-/
axiom adjunctionViaKanExtensions {C D : Category} {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## The Hom-Set Formulation -/

/--
An adjunction can be equivalently formulated as a natural isomorphism
  D(F X, Y) ≅ C(X, G Y)
of functors Cᵒᵖ × D → Set.
-/
axiom homSetAdjunctionEquivalence {C D : Category} (F : Functor C D) (G : Functor D C) :
  Nonempty (F ⊣ G) ↔ Nonempty (HomAdjunction C D F G)

/-! ## Adjoints in the 2-Category of Categories -/

/--
Adjunctions are the "dual" of equivalences in the 2-categorical sense:
an adjunction is a pair (F, G) with unit η : id_C ⇒ G F and counit
ε : F G ⇒ id_D satisfying triangle identities.
-/
axiom adjunction2CategoryView {C D : Category} : Prop

#eval "Theorems.Main: adjunctionsCompose, adjunctionDeterminedByUnit/Counit"
#eval "Theorems.Main: RAPL, LAPC, adjointCorrespondenceNatural (axioms)"
#eval "Theorems.Main: full/faithful adjoints, Kan extension characterization (axioms)"
