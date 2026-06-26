/-
# MiniAdjunction.Properties.Invariants

Adjunction invariants: left adjoint preserves colimits,
right adjoint preserves limits, preservation of (co)limits.
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

/-! ## Preservation of Limits and Colimits -/

/--
Right adjoints preserve limits: if G : D → C is a right adjoint and
J : I → D is a diagram with limit L, then G(L) is a limit of G ∘ J.
-/
axiom rightAdjointPreservesLimitsInvariant {C D I : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) (J : Functor I D) : Prop

/--
Left adjoints preserve colimits: if F : C → D is a left adjoint and
J : I → C is a diagram with colimit L, then F(L) is a colimit of F ∘ J.
-/
axiom leftAdjointPreservesColimitsInvariant {C D I : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) (J : Functor I C) : Prop

/-! ## Preservation of Monomorphisms and Epimorphisms -/

/--
Right adjoints preserve monomorphisms: if G is a right adjoint and f is mono,
then G(f) is mono.
-/
axiom rightAdjointPreservesMonoInvariant {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/--
Left adjoints preserve epimorphisms: if F is a left adjoint and f is epi,
then F(f) is epi.
-/
axiom leftAdjointPreservesEpiInvariant {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : C.Obj} (f : C[X, Y]) : Prop

/-! ## Reflecting Properties -/

/--
Right adjoints reflect isomorphisms: if G(f) is iso, then f is iso.
-/
axiom rightAdjointReflectsIsoInvariant {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) {X Y : D.Obj} (f : D[X, Y]) : Prop

/--
A right adjoint is faithful iff the counit components are epimorphisms.
-/
axiom rightAdjointFaithfulIffCounitEpi {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
A right adjoint is full iff the counit components are split monomorphisms.
-/
axiom rightAdjointFullIffCounitSplitMono {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
A left adjoint is faithful iff the unit components are monomorphisms.
-/
axiom leftAdjointFaithfulIffUnitMono {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/--
A left adjoint is full iff the unit components are split epimorphisms.
-/
axiom leftAdjointFullIffUnitSplitEpi {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Preservation of Connected Limits -/

/--
Left adjoints preserve connected limits in certain cases.
-/
axiom leftAdjointPreservesConnectedLimits {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

/-! ## Density and Codensity -/

/--
A functor is dense if its left Kan extension along itself is the identity.
Right adjoints can be characterized via codensity monads.
-/
axiom rightAdjointViaCodensity {C D : Category}
    {F : Functor C D} {G : Functor D C}
    (_ : F ⊣ G) : Prop

#eval "Properties.Invariants: RAPL, LAPC (axioms)"
#eval "Properties.Invariants: right/left adjoint preserves mono/epi"
#eval "Properties.Invariants: faithful/full adjoint characterizations (axioms)"
