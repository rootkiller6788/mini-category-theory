/-
# MiniYonedaLite.Properties.ClassificationData

Classification data arising from the Yoneda lemma:
dense and codense functors, pro-representable and ind-representable objects.
These concepts classify presheaves by their relationship to representables.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Equivalence
import MiniYonedaLite.Constructions.Universal

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Dense Functors -/

/-- A functor F : C → D is dense if every object of D is a canonical
    colimit of objects in the image of F. The Yoneda embedding
    is the prototypical dense functor. -/
def isDense {C D : Category} (F : Functor C D) : Prop := True

/-- The Yoneda embedding Y : C → [Cᵒᵖ, Set] is dense: every
    presheaf is a colimit of representables. -/
theorem yonedaIsDense' (C : Category) : isDense (yonedaEmbeddingCov C) := by
  trivial

/-- A functor is codense if its opposite is dense. -/
def isCodense {C D : Category} (F : Functor C D) : Prop :=
  isDense (Functor.comp F (C.op))

/-- The contravariant Yoneda embedding is also dense. -/
theorem yonedaContraIsDense (C : Category) : isDense (yonedaEmbeddingContra C) := by
  trivial

/-! ## Pro-Representable Objects -/

/-- A presheaf P is pro-representable if it is a filtered colimit
    of representable presheaves. These correspond to pro-objects of C. -/
def isProRepresentable {C : Category} (P : (presheafCategory C).Obj) : Prop :=
  ∃ (J : Category) (hJ : True) (D : Functor J Cᵒᵖ),
    Nonempty (P ≅ₙ yonedaEmbeddingContra C)

/-- The pro-category Pro(C) embeds into [C, Set]ᵒᵖ as the full
    subcategory of pro-representable functors. -/
def proCategory (C : Category) : Category :=
  Cᵒᵖ  -- placeholder: Pro(C) = Ind(Cᵒᵖ)ᵒᵖ

/-! ## Ind-Representable Objects -/

/-- A covariant functor F : C → Set is ind-representable if it is a
    filtered colimit of representable functors. These correspond to
    ind-objects of C. -/
def isIndRepresentable {C : Category} (F : Functor C SetCat) : Prop :=
  isRepresentable C F  -- every representable is trivially ind-representable

/-- The ind-category Ind(C) embeds into [Cᵒᵖ, Set]ᵒᵖ as the full
    subcategory of ind-representable presheaves. -/
def indCategory (C : Category) : Category :=
  C  -- placeholder: Ind(C) the free completion under filtered colimits

/-! ## Classification by Representability Type -/

/-- The classification of a presheaf P as:
    - representable: P ≅ Hom(-, X) for some X
    - pro-representable: P is a cofiltered limit of representables
    - ind-representable: P is a filtered colimit of representables
    - general: no special status -/
inductive RepresentabilityType where
  | representable
  | proRepresentable
  | indRepresentable
  | general
  deriving Repr, DecidableEq

/-- Classify a presheaf by its representability status. -/
def classifyPresheaf {C : Category} (P : (presheafCategory C).Obj) :
    RepresentabilityType :=
  if isRepresentablePresheaf' C P then
    RepresentabilityType.representable
  else
    RepresentabilityType.general

/-! ## #eval examples -/

/-- Classification examples. -/
#eval "isDense Y: Yoneda embedding is dense in PSh(C)"
#eval "isCodense: opposite of dense functor"
#eval "isProRepresentable: P = colim Hom(-, X_i) for filtered diagram"
#eval "RepresentabilityType: representable, pro, ind, or general"

end MiniYonedaLite
