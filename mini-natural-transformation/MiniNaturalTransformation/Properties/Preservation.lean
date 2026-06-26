/-
# MiniNaturalTransformation.Properties.Preservation

Properties preserved by whiskering and composition with natural
isomorphisms. Whiskering preserves monic/epic/iso componentwise properties.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Iso
import MiniNaturalTransformation.Properties.Invariants

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Whiskering Preserves Componentwise Monic -/

/--
Left whiskering preserves monicity: if α is componentwise monic,
then F*α is componentwise monic.
-/
theorem whiskerLeft_preserves_monic {C D E : Category}
    (F : Functor C D) {G H : Functor D E} (α : G ⇒ H)
    (hα : isComponentwiseMonic α) :
    isComponentwiseMonic (NaturalTransformation.whiskerLeft F α) := by
  intro X T a b h
  simp [NaturalTransformation.whiskerLeft] at h
  exact hα (F.mapObj X) a b h

/--
Left whiskering preserves epicity: if α is componentwise epic,
then F*α is componentwise epic.
-/
theorem whiskerLeft_preserves_epic {C D E : Category}
    (F : Functor C D) {G H : Functor D E} (α : G ⇒ H)
    (hα : isComponentwiseEpic α) :
    isComponentwiseEpic (NaturalTransformation.whiskerLeft F α) := by
  intro X T a b h
  simp [NaturalTransformation.whiskerLeft] at h
  exact hα (F.mapObj X) a b h

/-! ## Composition with Natural Isomorphism Preserves Properties -/

/--
If α : G ≅ₙ H is a natural isomorphism and β : F ⇒ G is componentwise monic,
then α.toNatTrans ∘ β : F ⇒ H is componentwise monic.
-/
theorem comp_with_natIso_preserves_monic {C D : Category} {F G H : Functor C D}
    (α : G ≅ₙ H) (β : F ⇒ G) (hβ : isComponentwiseMonic β) :
    isComponentwiseMonic (NaturalTransformation.vcomp α.toNatTrans β) := by
  intro X T a b hcomp
  have h_alpha_monic : isComponentwiseMonic α.toNatTrans := by
    intro X' T' a' b' h'
    apply_fun (λ t => D.comp (α.inv X') t) at h'
    simp [D.assoc, α.leftInv X', D.id_comp] at h'
    exact h'
  apply hβ X T a b
  apply h_alpha_monic X T
    (D.comp (β.component X) a) (D.comp (β.component X) b)
  calc
    D.comp (α.toNatTrans.component X) (D.comp (β.component X) a) =
      D.comp (D.comp (α.toNatTrans.component X) (β.component X)) a := by
      simp [D.assoc]
    _ = D.comp (D.comp (α.toNatTrans.component X) (β.component X)) b := by
      simpa [NaturalTransformation.vcomp, D.assoc] using hcomp
    _ = D.comp (α.toNatTrans.component X) (D.comp (β.component X) b) := by
      simp [D.assoc]

/--
If α : G ≅ₙ H is a natural isomorphism and β : F ⇒ G is componentwise epic,
then α.toNatTrans ∘ β : F ⇒ H is componentwise epic.
-/
theorem comp_with_natIso_preserves_epic {C D : Category} {F G H : Functor C D}
    (α : G ≅ₙ H) (β : F ⇒ G) (hβ : isComponentwiseEpic β) :
    isComponentwiseEpic (NaturalTransformation.vcomp α.toNatTrans β) := by
  intro X T a b hcomp
  have h_alpha_epic : isComponentwiseEpic α.toNatTrans := by
    intro X' T' a' b' h'
    apply_fun (λ t => D.comp t (α.inv X')) at h'
    simp [D.assoc, α.rightInv X', D.comp_id] at h'
    exact h'
  apply h_alpha_epic X T a b
  apply hβ X T
    (D.comp a (α.toNatTrans.component X))
    (D.comp b (α.toNatTrans.component X))
  calc
    D.comp (D.comp a (α.toNatTrans.component X)) (β.component X) =
      D.comp a (D.comp (α.toNatTrans.component X) (β.component X)) := by
      simp [D.assoc]
    _ = D.comp b (D.comp (α.toNatTrans.component X) (β.component X)) := by
      simpa [NaturalTransformation.vcomp, D.assoc] using hcomp
    _ = D.comp (D.comp b (α.toNatTrans.component X)) (β.component X) := by
      simp [D.assoc]

/-! ## #eval Examples -/

/-- Identity is preserved under left whiskering. -/
def idPreservedByWhiskerLeft : isComponentwiseMonic
    (NaturalTransformation.whiskerLeft idFunctor (NaturalTransformation.id idFunctor)) :=
  whiskerLeft_preserves_monic idFunctor (NaturalTransformation.id idFunctor)
    (by
      intro X T a b h
      simp [NaturalTransformation.id] at h
      exact h)

#eval "Properties.Preservation: whiskerLeft_preserves_monic, whiskerLeft_preserves_epic, comp_with_natIso_preserves_monic, comp_with_natIso_preserves_epic"
#eval s!"Whiskering preserves monic and epic properties"
#eval s!"Composition with natural iso preserves monic/epic"
