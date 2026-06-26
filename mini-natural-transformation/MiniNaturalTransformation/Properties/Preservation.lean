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

/-! ## Functoriality of Whiskering -/

/--
Whiskering is functorial in the natural transformation argument:
if α = β then F*α = F*β.
-/
theorem whiskerLeft_congr {C D E : Category}
    (F : Functor C D) {G H : Functor D E} {α β : G ⇒ H}
    (h : α = β) :
    NaturalTransformation.whiskerLeft F α = NaturalTransformation.whiskerLeft F β := by
  rw [h]

/--
Right whiskering is functorial in the natural transformation argument.
-/
theorem whiskerRight_congr {C D E : Category}
    {F G : Functor C D} {α β : F ⇒ G} (H : Functor D E)
    (h : α = β) :
    NaturalTransformation.whiskerRight α H = NaturalTransformation.whiskerRight β H := by
  rw [h]

/--
Left whiskering preserves natural isomorphisms: if α : G ≅ₙ H is a natural
isomorphism, then F*α : F∘G ≅ₙ F∘H is also a natural isomorphism.
-/
theorem whiskerLeft_preserves_iso {C D E : Category}
    (F : Functor C D) {G H : Functor D E} (α : G ≅ₙ H) :
    isNaturalIso (NaturalTransformation.whiskerLeft F α.toNatTrans) := by
  intro X
  refine ⟨H.mapHom (α.inv (F.mapObj X)), ?_, ?_⟩
  · simp [NaturalTransformation.whiskerLeft, ← H.preservesComp, α.leftInv (F.mapObj X)]
  · simp [NaturalTransformation.whiskerLeft, ← H.preservesComp, α.rightInv (F.mapObj X)]

/--
Right whiskering preserves natural isomorphisms: if α : F ≅ₙ G, then
α*H : F∘H ⇒ G∘H is pointwise iso (components H(α.inv X)).
-/
theorem whiskerRight_preserves_iso {C D E : Category}
    {F G : Functor C D} (α : F ≅ₙ G) (H : Functor D E) :
    isNaturalIso (NaturalTransformation.whiskerRight α.toNatTrans H) := by
  intro X
  refine ⟨H.mapHom (α.inv X), ?_, ?_⟩
  · simp [NaturalTransformation.whiskerRight, ← H.preservesComp, α.leftInv X]
  · simp [NaturalTransformation.whiskerRight, ← H.preservesComp, α.rightInv X]

/-! ## #eval Examples -/

/-- Identity is preserved under left whiskering. -/
def idPreservedByWhiskerLeft : isComponentwiseMonic
    (NaturalTransformation.whiskerLeft idFunctor (NaturalTransformation.id idFunctor)) :=
  whiskerLeft_preserves_monic idFunctor (NaturalTransformation.id idFunctor)
    (by
      intro X T a b h
      simp [NaturalTransformation.id] at h
      exact h)

/-- Reverse whiskered by identity is still an isomorphism. -/
def reverseWhiskeredById : isNaturalIso
    (NaturalTransformation.whiskerRight reverseNatIso.toNatTrans idFunctor) :=
  whiskerRight_preserves_iso reverseNatIso idFunctor

#eval "Properties.Preservation: whiskerLeft_preserves_monic, whiskerLeft_preserves_epic, comp_with_natIso_preserves_monic, comp_with_natIso_preserves_epic"
#eval "whiskerLeft_congr, whiskerRight_congr, whiskerLeft_preserves_iso, whiskerRight_preserves_iso"
#eval s!"Whiskering preserves monic and epic properties"
#eval s!"Composition with natural iso preserves monic/epic"
#eval s!"Whiskering preserves natural isomorphisms"
