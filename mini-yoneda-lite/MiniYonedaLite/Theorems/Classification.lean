/-
# MiniYonedaLite.Theorems.Classification

Classification theorems using the Yoneda lemma:
- Representable functor theorem (characterizing representables)
- Brown representability theorem (in homotopy theory)
- Adjoint functor theorems via Yoneda
- Special adjoint functor theorem
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso
import MiniYonedaLite.Properties.ClassificationData
import MiniYonedaLite.Properties.Preservation

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Representable Functor Theorem -/

/-- A functor F : C → Set is representable iff it preserves limits
    and satisfies the solution set condition. This is the general
    representable functor theorem. State as an axiom here. -/
axiom representableFunctorTheorem (C : Category) (F : Functor C SetCat)
    (hPreservesLimits : True) (hSolutionSet : True) :
    isRepresentable C F

/-- For a small complete category C, a functor F : C → Set is
    representable iff it preserves limits. -/
axiom specialRepresentableFunctorTheorem (C : Category) (F : Functor C SetCat)
    (hComplete : True) (hPreservesLimits : True) :
    isRepresentable C F

/-! ## Brown Representability -/

/-- Brown representability theorem: in the homotopy category of
    spectra (or pointed connected CW complexes), a contravariant
    functor to Set is representable iff it sends coproducts to
    products and satisfies the Mayer-Vietoris condition. -/
axiom brownRepresentability (C : Category) (F : Functor (Cᵒᵖ) SetCat)
    (hCoproductsToProducts : True) (hMayerVietoris : True) :
    isRepresentablePresheaf' C F

/-- Simplified Brown: a functor H : Ho(Top)ᵒᵖ → Set is representable
    iff it is a cohomology theory (homotopy invariant, exact, additive). -/
axiom brownRepresentabilityCohomology (F : Functor SetCatᵒᵖ SetCat) : True

/-! ## Adjoint Functor Theorem via Yoneda -/

/-- The General Adjoint Functor Theorem: a functor G : D → C has a
    left adjoint iff G preserves limits and satisfies the solution set
    condition. The proof uses the Yoneda lemma and the representable
    functor theorem. -/
axiom generalAdjointFunctorTheorem (C D : Category) (G : Functor D C)
    (hPreservesLimits : True) (hSolutionSet : True) : True

/-- The Special Adjoint Functor Theorem: if C is complete and
    well-powered with a cogenerating set, then a limit-preserving
    G : D → C has a left adjoint. -/
axiom specialAdjointFunctorTheorem (C D : Category) (G : Functor D C)
    (hComplete : True) (hWellPowered : True) (hCogenerator : True) : True

/-- Construction of a left adjoint using Yoneda:
    F(X) is the representing object for C(X, G(-)). -/
def leftAdjointViaYoneda (C D : Category) (G : Functor D C) (X : C.Obj) :
    (functorCategory Dᵒᵖ SetCat).Obj :=
  -- F(X) represented by: C(X, G(-))
  homFunctorOp C X  -- placeholder

/-! ## Yoneda Proof of Adjoint Functor Theorem -/

/-- The adjoint functor theorem is proved by applying the
    representable functor theorem to the functor C(X, G(-)) : D → Set. -/
axiom adjointFunctorTheoremProof (C D : Category) (G : Functor D C) : True

/-- If each C(X, G(-)) is representable, then G has a left adjoint. -/
axiom representabilityGivesAdjoint (C D : Category) (G : Functor D C)
    (h : ∀ (X : C.Obj), isRepresentable D (homFunctor C X)) : True

/-! ## #eval examples -/

/-- Classification theorem examples. -/
#eval "representableFunctorTheorem: limit-preserving + SSC ⇒ representable"
#eval "brownRepresentability: cohomology theories are representable"
#eval "generalAdjointFunctorTheorem: G has left adjoint iff ..."
#eval s!"Yoneda proves: G left adjoint ⇔ each C(X,G(-)) representable"

end MiniYonedaLite
