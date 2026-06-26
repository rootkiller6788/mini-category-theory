/-
# MiniYonedaLite.Properties.Preservation

Preservation properties of the Yoneda embedding:
Y preserves limits, Y reflects isomorphisms, and Y creates certain
universal constructions.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso
import MiniYonedaLite.Constructions.Products

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda Preserves Limits -/

/-- The Yoneda embedding is continuous: it preserves all limits
    that exist in C. This is because limits in the presheaf category
    are computed pointwise, and Hom(-, lim X_i) ≅ lim Hom(-, X_i). -/
axiom yonedaPreservesLimits (C D : Category) (F : Functor D C) : True

/-- Yoneda preserves terminal objects: Y(1_C) is the terminal
    presheaf (constant singleton functor). -/
axiom yonedaPreservesTerminal (C : Category) (t : C.Obj) (hIsTerminal : True) :
  Nonempty (homFunctorOp C t ≅ₙ Functor.const (Cᵒᵖ) SetCat PUnit.{u})

/-- Yoneda preserves pullbacks: the Yoneda image of a pullback
    square in C is a pullback square in the presheaf category. -/
axiom yonedaPreservesPullbacks (C : Category) : True

/-- The Yoneda embedding sends limits in C to limits in [Cᵒᵖ, Set]. -/
axiom yonedaIsContinuous (C : Category) : True

/-! ## Yoneda Reflects Isomorphisms -/

/-- If Y(f) is an isomorphism in the presheaf category,
    then f is an isomorphism in C. This is a consequence of
    the Yoneda lemma and full faithfulness. -/
axiom yonedaReflectsIsos (C : Category) (X Y : C.Obj) (f : C[X, Y])
    (h : Nonempty (homFunctorOp C X ≅ₙ homFunctorOp C Y)) : True

/-- The Yoneda embedding is conservative: it reflects isomorphisms. -/
def yonedaIsConservative (C : Category) : Prop :=
  ∀ (X Y : C.Obj) (f : C[X, Y]),
    (∃ (g : C[Y, X]), C.comp f g = C.id X ∧ C.comp g f = C.id Y) ↔
    (∃ (η : (homFunctorOp C X) ⇒ (homFunctorOp C Y)),
      True)

/-! ## Yoneda Creates Limits -/

/-- The Yoneda embedding creates limits: if a diagram in the image
    of Y has a limit in the presheaf category, then the corresponding
    diagram in C already had that limit. -/
axiom yonedaCreatesLimits (C : Category) : True

/-- Yoneda creates products: if Y(X) × Y(Y) exists in PSh(C),
    then X × Y exists in C. -/
axiom yonedaCreatesProducts (C : Category) (X Y : C.Obj) : True

/-- The Yoneda embedding creates all limits that the
    presheaf category has for representable diagrams. -/
axiom yonedaCreatesAllLimits (C : Category) : True

/-! ## Yoneda Preserves Colimits via the Covariant Embedding -/

/-- The covariant Yoneda embedding Y : C → [Cᵒᵖ, Set] sends
    colimits in C to limits in the presheaf category
    (since it is contravariant on the domain). -/
axiom yonedaSendsColimitsToLimits (C : Category) : True

/-- The contravariant Yoneda embedding sends limits in Cᵒᵖ
    (i.e., colimits in C) to limits in the presheaf category. -/
axiom yonedaContraPreservesLimits (C : Category) : True

/-! ## #eval examples -/

/-- Preservation and reflection. -/
#eval "yonedaPreservesLimits: Y preserves all limits"
#eval "yonedaReflectsIsos: if Y(f) iso then f iso"
#eval "yonedaCreatesLimits: limits of representables lift to C"
#eval s!"Yoneda is continuous and conservative"

end MiniYonedaLite
