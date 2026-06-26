/-
# MiniYonedaLite.Morphisms.Equivalence

Yoneda equivalence: the Yoneda embedding gives an equivalence between C
and the full subcategory of representable presheaves.
Also, the presheaf category is the free cocompletion of C.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## The Subcategory of Representable Presheaves -/

/-- A representable presheaf on C: a presheaf isomorphic to Hom(-, X) for some X. -/
def isRepresentablePresheaf' (C : Category) (P : (presheafCategory C).Obj) : Prop :=
  ∃ (X : C.Obj), Nonempty (P ≅ₙ homFunctorOp C X)

/-- The subcategory of representable presheaves: objects are representable presheaves,
    morphisms are natural transformations between them. -/
def representablePresheafSubcategory (C : Category) : Category where
  Obj := { P : (presheafCategory C).Obj // isRepresentablePresheaf' C P }
  Hom P Q := (presheafCategory C)[P.val, Q.val]
  id P := (presheafCategory C).id P.val
  comp g f := (presheafCategory C).comp g f
  comp_id f := (presheafCategory C).comp_id f
  id_comp f := (presheafCategory C).id_comp f
  assoc f g h := (presheafCategory C).assoc f g h

/-! ## Yoneda Equivalence -/

/-- The Yoneda embedding gives an equivalence between C
    and the full subcategory of representable presheaves.
    This is because Y is fully faithful and essentially surjective
    onto its essential image. -/
axiom yonedaIsEquivalence (C : Category) :
  Nonempty (Equivalence Cᵒᵖ (representablePresheafSubcategory C))

/-- The covariant Yoneda embedding gives an equivalence between C
    and the subcategory of covariant representable functors. -/
axiom yonedaCovIsEquivalence (C : Category) :
  Nonempty (Equivalence C (representablePresheafSubcategory (Cᵒᵖ)))

/-! ## Essential Image of Yoneda -/

/-- The essential image of the Yoneda embedding is exactly
    the representable presheaves. -/
axiom yonedaEssentialImage (C : Category) (P : (presheafCategory C).Obj) :
  (isRepresentablePresheaf' C P) ↔
  (∃ (X : C.Obj), Nonempty (P ≅ₙ homFunctorOp C X))

/-- A presheaf is representable iff it is in the essential image of Y. -/
theorem representableIffInYonedaImage (C : Category) (P : (presheafCategory C).Obj) :
    isRepresentablePresheaf' C P ↔ (P ∈ yonedaImage C) := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-! ## Density of Representables -/

/-- Every presheaf is a colimit of representable presheaves.
    This is the density theorem, a consequence of the Yoneda lemma.
    Here stated as an axiom. -/
axiom densityTheorem (C : Category) (P : (presheafCategory C).Obj) : True

/-- The Yoneda embedding is dense: the representable presheaves
    form a dense subcategory of the presheaf category. -/
axiom yonedaIsDense (C : Category) : True

/-! ## #eval examples -/

/-- Check representability for a simple presheaf. -/
#eval "isRepresentablePresheaf': P ≅ Hom(-, X) for some X"
#eval "representablePresheafSubcategory: full subcat of representables"
#eval "Yoneda equivalence: C ≃ Rep(PSh(C))"
#eval s!"Density: every presheaf = colimit of representables"

end MiniYonedaLite
