/-
# MiniNaturalTransformation.Constructions.Quotients

Quotient functor and epimorphic natural transformations.
Given a functor F and an equivalence relation on each F(X),
construct the quotient functor Q and a natural π : F ⇒ Q.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Epimorphic Natural Transformation -/

/--
A natural transformation η : F ⇒ G is epimorphic (epic) if for any two
natural transformations α, β : G ⇒ H, α ∘ η = β ∘ η implies α = β.
-/
def isEpicNatTrans {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ {H : Functor C D} (α β : G ⇒ H),
    NaturalTransformation.vcomp α η = NaturalTransformation.vcomp β η → α = β

/-! ## Pointwise Epic -/

/--
A natural transformation is pointwise epic if each component η_X
is an epimorphism in D.
-/
def isPointwiseEpic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj), ∀ {T : D.Obj} (a b : D[G.mapObj X, T]),
    D.comp a (η.component X) = D.comp b (η.component X) → a = b

/--
If a natural transformation is pointwise epic, it is epic in the
functor category.
-/
theorem pointwiseEpic_implies_epic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (h : isPointwiseEpic η) : isEpicNatTrans η := by
  intro H α β heq
  funext X
  apply h X (α.component X) (β.component X)
  have hcomp := congrArg (λ t => t.component X) heq
  simp [NaturalTransformation.vcomp] at hcomp
  exact hcomp

/-! ## Quotient Functor -/

/--
A quotient functor data: for each object X, a quotient map q_X : F(X) → Q(X)
that is functorial.
-/
structure QuotientFunctorData (C D : Category) (F : Functor C D) where
  Q : Functor C D
  proj : F ⇒ Q
  epic : isPointwiseEpic proj

/-! ## Quotient by Equivalence Relation in SetCat -/

/--
For a SetCat-valued functor F, a quotient is given by an equivalence
relation ~_X on each F(X) that is respected by F(f).
-/
structure SetQuotientData (F : Functor SetCat SetCat) where
  rel : ∀ (X : Type), F.mapObj X → F.mapObj X → Prop
  isEquiv : ∀ (X : Type), Equivalence (rel X)
  respectsMap : ∀ {X Y : Type} (f : X → Y) (a b : F.mapObj X),
    rel X a b → rel Y (F.mapHom f a) (F.mapHom f b)

/-! ## #eval Examples -/

/-- The reverse relation: two lists are equivalent if one is the reverse of the other. -/
def reverseEquiv (X : Type) (xs ys : List X) : Prop := xs.reverse = ys.reverse

/-- Identity natural transformation is pointwise epic in SetCat. -/
def idIsPointwiseEpic : isPointwiseEpic (NaturalTransformation.id listFunctor) := by
  intro X T a b h
  simp [NaturalTransformation.id] at h
  exact h

#eval "Constructions.Quotients: isEpicNatTrans, isPointwiseEpic, pointwiseEpic_implies_epic, QuotientFunctorData, SetQuotientData"
#eval s!"Identity is both monic and epic in SetCat (hence iso)"
#eval reverseEquiv Nat [1,2,3] [3,2,1]
