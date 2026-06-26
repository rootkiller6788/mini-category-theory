/-
# MiniNaturalTransformation.Constructions.Products

Pointwise products of functors and natural transformations between
product functors. If D has products, the functor category [C, D] also
has products, computed pointwise.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Pointwise Product of Functors -/

/--
The pointwise product of two SetCat-valued functors F, G : C → SetCat
is the functor X ↦ F(X) × G(X).
-/
def pointwiseProduct (F G : Functor SetCat SetCat) : Functor SetCat SetCat where
  mapObj X := F.mapObj X × G.mapObj X
  mapHom {X Y} f (x, y) := (F.mapHom f x, G.mapHom f y)
  preservesId X := by
    funext p; rcases p with ⟨x, y⟩; simp
  preservesComp {X Y Z} f g := by
    funext p; rcases p with ⟨x, y⟩; simp

/-! ## Natural Transformation between Products -/

/--
Given natural transformations α : F ⇒ F' and β : G ⇒ G', we get
a natural transformation α × β : F × G ⇒ F' × G'.
-/
def productNatTrans {F F' G G' : Functor SetCat SetCat}
    (α : F ⇒ F') (β : G ⇒ G') : pointwiseProduct F G ⇒ pointwiseProduct F' G' where
  component X := λ (x, y) => (α.component X x, β.component X y)
  naturality {X Y} f := by
    funext ⟨x, y⟩
    simp

/-! ## Projection Natural Transformations -/

/--
First projection: π₁ : F × G ⇒ F.
-/
def fstProj (F G : Functor SetCat SetCat) : pointwiseProduct F G ⇒ F where
  component X := λ (x, _) => x
  naturality {X Y} f := by funext ⟨x, y⟩; simp

/--
Second projection: π₂ : F × G ⇒ G.
-/
def sndProj (F G : Functor SetCat SetCat) : pointwiseProduct F G ⇒ G where
  component X := λ (_, y) => y
  naturality {X Y} f := by funext ⟨x, y⟩; simp

/-! ## Universal Property of Pointwise Products -/

/--
Given α : H ⇒ F and β : H ⇒ G, there is a unique ⟨α, β⟩ : H ⇒ F × G
making the projection triangles commute.
-/
def pairNatTrans {H F G : Functor SetCat SetCat}
    (α : H ⇒ F) (β : H ⇒ G) : H ⇒ pointwiseProduct F G where
  component X x := (α.component X x, β.component X x)
  naturality {X Y} f := by
    funext x; simp

/--
First projection composed with pairing equals the first component.
-/
theorem fst_pair {H F G : Functor SetCat SetCat}
    (α : H ⇒ F) (β : H ⇒ G) :
    NaturalTransformation.vcomp (fstProj F G) (pairNatTrans α β) = α := by
  funext X x; simp [pairNatTrans, fstProj, NaturalTransformation.vcomp]

/--
Second projection composed with pairing equals the second component.
-/
theorem snd_pair {H F G : Functor SetCat SetCat}
    (α : H ⇒ F) (β : H ⇒ G) :
    NaturalTransformation.vcomp (sndProj F G) (pairNatTrans α β) = β := by
  funext X x; simp [pairNatTrans, sndProj, NaturalTransformation.vcomp]

/-! ## Diagonal Natural Transformation -/

/--
The diagonal natural transformation Δ : F ⇒ F × F is the pairing of the
identity natural transformation with itself.
-/
def diagonalNatTrans (F : Functor SetCat SetCat) : F ⇒ pointwiseProduct F F :=
  pairNatTrans (NaturalTransformation.id F) (NaturalTransformation.id F)

/--
The diagonal followed by first projection is the identity.
-/
theorem diag_fst (F : Functor SetCat SetCat) :
    NaturalTransformation.vcomp (fstProj F F) (diagonalNatTrans F) =
    NaturalTransformation.id F := by
  funext X x; simp [diagonalNatTrans, fstProj, pairNatTrans, NaturalTransformation.id,
    NaturalTransformation.vcomp]

/--
The diagonal followed by second projection is the identity.
-/
theorem diag_snd (F : Functor SetCat SetCat) :
    NaturalTransformation.vcomp (sndProj F F) (diagonalNatTrans F) =
    NaturalTransformation.id F := by
  funext X x; simp [diagonalNatTrans, sndProj, pairNatTrans, NaturalTransformation.id,
    NaturalTransformation.vcomp]

/-! ## Pointwise Coproduct of Functors -/

/--
The pointwise coproduct (sum) of two SetCat-valued functors F, G : C → SetCat
is the functor X ↦ F(X) ⊕ G(X) (using Sum type).
-/
def pointwiseCoproduct (F G : Functor SetCat SetCat) : Functor SetCat SetCat where
  mapObj X := F.mapObj X ⊕ G.mapObj X
  mapHom {X Y} f := Sum.map (F.mapHom f) (G.mapHom f)
  preservesId X := by
    funext s; cases s <;> simp
  preservesComp {X Y Z} f g := by
    funext s; cases s <;> simp

/--
First injection: ι₁ : F ⇒ F ⊕ G.
-/
def inlNatTrans (F G : Functor SetCat SetCat) : F ⇒ pointwiseCoproduct F G where
  component X x := Sum.inl x
  naturality {X Y} f := by funext x; simp

/--
Second injection: ι₂ : G ⇒ F ⊕ G.
-/
def inrNatTrans (F G : Functor SetCat SetCat) : G ⇒ pointwiseCoproduct F G where
  component X y := Sum.inr y
  naturality {X Y} f := by funext y; simp

/-! ## #eval Examples -/

/-- Pointwise product of List × Option. -/
def listTimesMaybe := pointwiseProduct listFunctor maybeFunctor

/-- Fst projection at Nat. -/
#eval "Constructions.Products: pointwiseProduct, productNatTrans, fstProj, sndProj, pairNatTrans"
#eval "diagonalNatTrans, diag_fst, diag_snd, pointwiseCoproduct, inlNatTrans, inrNatTrans"
#eval fstProj listFunctor maybeFunctor |>.component Nat (([1,2,3], some "hello"))
#eval s!"Product of functors: X → F(X) × G(X)"
#eval s!"Coproduct of functors: X → F(X) ⊕ G(X)"
#eval inlNatTrans listFunctor maybeFunctor |>.component Nat [1,2,3]
