/-
# MiniNaturalTransformation.Morphisms.Equivalence

Natural equivalence: equivalence of functors, isomorphic functors are
equivalent. Two functors F, G : C → D are naturally equivalent if there
exists a natural isomorphism F ≅ₙ G.
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

/-! ## Natural Equivalence -/

/--
Two functors F, G : C → D are naturally equivalent if there exists
a natural isomorphism between them.
-/
def areNaturallyEquivalent {C D : Category} (F G : Functor C D) : Prop :=
  Nonempty (F ≅ₙ G)

/--
Natural equivalence is reflexive: every functor is equivalent to itself.
-/
theorem naturallyEquivalent_refl {C D : Category} (F : Functor C D) :
    areNaturallyEquivalent F F :=
  ⟨NaturalIsomorphism.id F⟩

/--
Natural equivalence is symmetric.
-/
theorem naturallyEquivalent_symm {C D : Category} {F G : Functor C D}
    (h : areNaturallyEquivalent F G) : areNaturallyEquivalent G F := by
  rcases h with ⟨α⟩
  exact ⟨α.symm⟩

/--
Natural equivalence is transitive.
-/
theorem naturallyEquivalent_trans {C D : Category} {F G H : Functor C D}
    (h₁ : areNaturallyEquivalent F G) (h₂ : areNaturallyEquivalent G H) :
    areNaturallyEquivalent F H := by
  rcases h₁ with ⟨α⟩
  rcases h₂ with ⟨β⟩
  exact ⟨NaturalIsomorphism.comp β α⟩

/-! ## Isomorphic Functors are Equivalent -/

/--
If F is isomorphic to G in the functor category [C, D], then they
are naturally equivalent. This is essentially the same statement.
-/
theorem iso_implies_naturallyEquivalent {C D : Category} {F G : Functor C D}
    (α : F ≅ₙ G) : areNaturallyEquivalent F G := ⟨α⟩

/-! ## Equivalent Functors and Sets -/

/--
For SetCat-valued functors, equivalence means there are family bijections
F(X) → G(X) that are natural.
-/
def equivOfSetValued {C : Category} {F G : Functor C SetCat}
    (α : F ≅ₙ G) (X : C.Obj) : (F.mapObj X → G.mapObj X) × (G.mapObj X → F.mapObj X) :=
  (α.toNatTrans.component X, α.inv X)

/--
A natural equivalence on SetCat-valued functors gives a bijection for each X.
-/
theorem equivOfSetValued_bijection {C : Category} {F G : Functor C SetCat}
    (α : F ≅ₙ G) (X : C.Obj) (x : F.mapObj X) :
    (α.inv X) ((α.toNatTrans.component X) x) = x := by
  have h := α.leftInv X
  funext _ at h
  have h' := congrFun h x
  simp at h'
  exact h'

/--
The other direction of the bijection: applying α_X then its inverse returns
the element.
-/
theorem equivOfSetValued_bijection_right {C : Category} {F G : Functor C SetCat}
    (α : F ≅ₙ G) (X : C.Obj) (y : G.mapObj X) :
    (α.toNatTrans.component X) ((α.inv X) y) = y := by
  have h := α.rightInv X
  funext _ at h
  have h' := congrFun h y
  simp at h'
  exact h'

/-! ## Natural Equivalence Preserves Structure -/

/--
Natural equivalence preserves the property of being a natural isomorphism.
If F ≅ₙ G and α : H ⇒ K is a natural isomorphism in [C, D], then the
transported morphism is also a natural isomorphism.
-/
theorem natEquiv_preserves_natIso {C D : Category} {F G : Functor C D}
    (equiv : F ≅ₙ G) : isNaturalIso equiv.toNatTrans := by
  intro X
  refine ⟨equiv.inv X, equiv.leftInv X, equiv.rightInv X⟩

/--
A composition of natural equivalences is a natural equivalence.
-/
theorem comp_natEquiv {C D : Category} {F G H : Functor C D}
    (α : F ≅ₙ G) (β : G ≅ₙ H) : areNaturallyEquivalent F H :=
  naturallyEquivalent_trans ⟨α⟩ ⟨β⟩

/-! ## #eval Examples -/

/-- listFunctor is naturally equivalent to itself. -/
def listSelfEquiv : areNaturallyEquivalent listFunctor listFunctor :=
  naturallyEquivalent_refl listFunctor

/-- reverse is a natural isomorphism, hence an equivalence. -/
def reverseEquiv : areNaturallyEquivalent listFunctor listFunctor :=
  ⟨reverseNatIso⟩

#eval "Morphisms.Equivalence: areNaturallyEquivalent, refl, symm, trans, iso_implies_naturallyEquivalent"
#eval "equivOfSetValued_bijection_right, natEquiv_preserves_natIso, comp_natEquiv"
#eval s!"listFunctor naturally equivalent to itself: {listSelfEquiv}"
#eval "Natural equivalence is an equivalence relation on functors"
#eval "reverse is a natural equivalence on listFunctor"
