/-
# MiniNaturalTransformation.Properties.Invariants

Natural transformation properties: isMonic (componentwise monic),
isEpic (componentwise epic), and isIso (componentwise iso).
These are invariants of natural transformations under various operations.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Iso

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Componentwise Monic -/

/--
A natural transformation is componentwise monic if each component
is monic in the target category.
-/
def isComponentwiseMonic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj) {T : D.Obj} (a b : D[T, F.mapObj X]),
    D.comp (η.component X) a = D.comp (η.component X) b → a = b

/-! ## Componentwise Epic -/

/--
A natural transformation is componentwise epic if each component
is epic in the target category.
-/
def isComponentwiseEpic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj) {T : D.Obj} (a b : D[G.mapObj X, T]),
    D.comp a (η.component X) = D.comp b (η.component X) → a = b

/-! ## Componentwise Iso -/

/--
A natural transformation is componentwise iso if each component is
an isomorphism. This is equivalent to being a natural isomorphism.
-/
def isComponentwiseIso {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj), ∃ (inv : D[G.mapObj X, F.mapObj X]),
    D.comp inv (η.component X) = D.id (F.mapObj X) ∧
    D.comp (η.component X) inv = D.id (G.mapObj X)

/--
A natural transformation is componentwise iso iff it is a natural isomorphism.
-/
theorem componentwiseIso_iff_natIso {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : isComponentwiseIso η ↔ isNaturalIso η := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-! ## Vertical Composition Preserves Monic/Epic -/

/--
If α and β are componentwise monic, then β ∘ α is componentwise monic.
-/
theorem vcomp_preserves_monic {C D : Category} {F G H : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H)
    (hα : isComponentwiseMonic α) (hβ : isComponentwiseMonic β) :
    isComponentwiseMonic (NaturalTransformation.vcomp β α) := by
  intro X T a b h
  have hcomp : D.comp (β.component X) (D.comp (α.component X) a) =
               D.comp (β.component X) (D.comp (α.component X) b) := by
    simpa [NaturalTransformation.vcomp, D.assoc] using h
  have h' := hβ X (D.comp (α.component X) a) (D.comp (α.component X) b) hcomp
  exact hα X a b h'

/--
If α and β are componentwise epic, then β ∘ α is componentwise epic.
-/
theorem vcomp_preserves_epic {C D : Category} {F G H : Functor C D}
    (α : F ⇒ G) (β : G ⇒ H)
    (hα : isComponentwiseEpic α) (hβ : isComponentwiseEpic β) :
    isComponentwiseEpic (NaturalTransformation.vcomp β α) := by
  intro X T a b h
  have hcomp : D.comp (D.comp a (β.component X)) (α.component X) =
               D.comp (D.comp b (β.component X)) (α.component X) := by
    simpa [NaturalTransformation.vcomp, D.assoc] using h
  have h' := hα X (D.comp a (β.component X)) (D.comp b (β.component X)) hcomp
  exact hβ X a b h'

/-! ## #eval Examples -/

/-- Identity natural transformation is componentwise monic in SetCat. -/
def idComponentwiseMonic : isComponentwiseMonic (NaturalTransformation.id listFunctor) := by
  intro X T a b h
  simp [NaturalTransformation.id] at h
  exact h

/-- Identity natural transformation is componentwise epic in SetCat. -/
def idComponentwiseEpic : isComponentwiseEpic (NaturalTransformation.id listFunctor) := by
  intro X T a b h
  simp [NaturalTransformation.id] at h
  exact h

#eval "Properties.Invariants: isComponentwiseMonic, isComponentwiseEpic, isComponentwiseIso, vcomp_preserves_monic, vcomp_preserves_epic"
#eval s!"Identity is both monic and epic componentwise"
#eval s!"Vertical composition preserves monic and epic properties"
