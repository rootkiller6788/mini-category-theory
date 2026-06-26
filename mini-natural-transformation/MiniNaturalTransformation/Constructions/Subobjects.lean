/-
# MiniNaturalTransformation.Constructions.Subobjects

Subfunctors, pointwise subobjects, and monic natural transformations.
A subfunctor S of F is a functor together with a monic natural
transformation S ⇒ F.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Subfunctor -/

/--
A subfunctor S of a functor F : C → D is a functor S : C → D together with
a monic natural transformation ι : S ⇒ F (componentwise monic).
-/
structure Subfunctor {C D : Category} (F : Functor C D) where
  S : Functor C D
  inclusion : S ⇒ F
  isMonic : ∀ (X : C.Obj), ∀ {a b : D[S.mapObj X, S.mapObj X]},
    D.comp (inclusion.component X) a = D.comp (inclusion.component X) b → a = b

/-! ## Pointwise Subobject -/

/--
A pointwise subobject condition: for each X, the component inclusion_X
is monic in D. This is the definition of a monic natural transformation.
-/
def isPointwiseMonic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj), ∀ {T : D.Obj} (a b : D[T, F.mapObj X]),
    D.comp (η.component X) a = D.comp (η.component X) b → a = b

/-! ## Monic Natural Transformation -/

/--
A natural transformation η : F ⇒ G is monic if for any two natural
transformations α, β : H ⇒ F, η ∘ α = η ∘ β implies α = β.
-/
def isMonicNatTrans {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ {H : Functor C D} (α β : H ⇒ F),
    NaturalTransformation.vcomp η α = NaturalTransformation.vcomp η β → α = β

/--
If a natural transformation is pointwise monic, it is monic as a
natural transformation in the functor category.
-/
theorem pointwiseMonic_implies_monic {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (h : isPointwiseMonic η) : isMonicNatTrans η := by
  intro H α β heq
  funext X
  apply h X (α.component X) (β.component X)
  have hcomp := congrArg (λ t => t.component X) heq
  simp [NaturalTransformation.vcomp] at hcomp
  exact hcomp

/-! ## Subobject via SetCat -/

/--
For SetCat-valued functors, a subfunctor is given by specifying
for each X a subset S(X) ⊆ F(X), closed under the functor action.
-/
structure SetSubfunctor (F : Functor SetCat SetCat) where
  pred : ∀ (X : Type), F.mapObj X → Prop
  closedUnderMap : ∀ {X Y : Type} (f : X → Y) (x : F.mapObj X),
    pred X x → pred Y (F.mapHom f x)

/-! ## Epimorphic Natural Transformation (Dual) -/

/--
A natural transformation η : F ⇒ G is epic (in the functor category)
if for any α, β : G ⇒ H with α ∘ η = β ∘ η, we have α = β.
-/
def isEpicNatTrans' {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ {H : Functor C D} (α β : G ⇒ H),
    NaturalTransformation.vcomp α η = NaturalTransformation.vcomp β η → α = β

/--
Dual to subobjects: an epimorphic natural transformation η : F ⇒ G
expresses G as a quotient of F (pointwise).
-/
def isPointwiseEpic' {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) : Prop :=
  ∀ (X : C.Obj) {T : D.Obj} (a b : D[G.mapObj X, T]),
    D.comp a (η.component X) = D.comp b (η.component X) → a = b

/--
Pointwise epic implies epic in the functor category.
-/
theorem pointwiseEpic_implies_epic' {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (h : isPointwiseEpic' η) : isEpicNatTrans' η := by
  intro H α β heq
  funext X
  apply h X (α.component X) (β.component X)
  have hcomp := congrArg (λ t => t.component X) heq
  simp [NaturalTransformation.vcomp] at hcomp
  exact hcomp

/-! ## Subfunctor Lattice -/

/--
The intersection of two subfunctors S₁, S₂ of F: pointwise intersection
of their defining predicates (for SetCat-valued functors).
-/
def intersectSubfunctors (F : Functor SetCat SetCat)
    (S₁ S₂ : SetSubfunctor F) : SetSubfunctor F where
  pred X x := S₁.pred X x ∧ S₂.pred X x
  closedUnderMap {X Y} f x h := by
    rcases h with ⟨h₁, h₂⟩
    exact ⟨S₁.closedUnderMap f x h₁, S₂.closedUnderMap f x h₂⟩

/--
The union of two subfunctors S₁, S₂ of F: pointwise union.
-/
def unionSubfunctors (F : Functor SetCat SetCat)
    (S₁ S₂ : SetSubfunctor F) : SetSubfunctor F where
  pred X x := S₁.pred X x ∨ S₂.pred X x
  closedUnderMap {X Y} f x h := by
    rcases h with (h₁ | h₂)
    · exact Or.inl (S₁.closedUnderMap f x h₁)
    · exact Or.inr (S₂.closedUnderMap f x h₂)

/-! ## #eval Examples -/

/-- The subfunctor of nonempty lists: S(X) = {xs : List X | xs ≠ []}. -/
def nonemptyPred : ∀ (X : Type), List X → Prop := λ X xs => xs ≠ []

/-- The subfunctor of even-length lists. -/
def evenLengthPred (X : Type) (xs : List X) : Prop := xs.length % 2 = 0

/-- Identity natural transformation is pointwise monic in SetCat. -/
def idIsPointwiseMonic : isPointwiseMonic (NaturalTransformation.id listFunctor) := by
  intro X T a b h
  simp [NaturalTransformation.id] at h
  exact h

#eval "Constructions.Subobjects: Subfunctor, isPointwiseMonic, isMonicNatTrans, pointwiseMonic_implies_monic, SetSubfunctor"
#eval "intersectSubfunctors, unionSubfunctors, evenLengthPred"
#eval s!"Identity natural transformation is pointwise monic"
#eval s!"nonemptyPred on List Nat 3: {nonemptyPred Nat ([1,2,3] : List Nat)}"
#eval evenLengthPred Nat [1,2,3,4]
