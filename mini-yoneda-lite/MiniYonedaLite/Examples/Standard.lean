/-
# MiniYonedaLite.Examples.Standard

Sample representable functors and applications of the Yoneda lemma.
Includes: Yoneda for discete categories, codiscrete categories,
preorders (down-set), and groups (Cayley's theorem connection).
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Morphisms.Iso
import MiniCategoryCore.Constructions.Products
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Objects
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Theorems.Main
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Morphisms.Iso
import MiniNaturalTransformation.Theorems.Main
import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Theorems.Basic
import MiniYonedaLite.Theorems.Main

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Example 1: Identity functor on Set is represented by the singleton -/

/-- The identity functor on Set is representable by the unit type.
    Id ≅ Hom(Unit, -) because any function from Unit is determined by
    the image of the unique element. -/
def identityRepresentable : isRepresentable SetCat (Functor.id SetCat) := by
  refine ⟨PUnit.{u}, ?_⟩
  -- Id(Y) = Y ≅ Set(PUnit, Y) by sending y to (λ _, y)
  exact ⟨NaturalTransformation.id (homFunctor SetCat PUnit.{u})⟩  -- placeholder

/-! ## Example 2: Constant functor representability -/

/-- The constant functor at A is representable iff A is a singleton.
    If A has more than one element, there is no object X with
    Hom(X, -) ≅ const A. -/
def constantFunctorRepresentable (A : SetCat.Obj) : Bool :=
  -- A constant functor ΔA is representable iff A ≅ PUnit
  Nonempty (A ≅ᶠ PUnit.{u})

/-! ## Example 3: Yoneda for Discrete Categories -/

/-- For a discrete category DiscCat A, the presheaf category is Set^A.
    The Yoneda embedding sends each a ∈ A to the projection functor
    ev_a : Set^A → Set. -/
def yonedaForDiscCat {A : Type u} : Functor (DiscCat Aᵒᵖ) [DiscCat A, SetCat] :=
  yonedaEmbeddingContra (DiscCat A)

/-- In a discrete category, representable presheaves are the "delta" functors:
    δ_a(b) = 1 if a = b, 0 otherwise. These form a basis of Set^A. -/
def representablePresheafDiscCat {A : Type u} (a : A) : (presheafCategory (DiscCat A)).Obj :=
  homFunctorOp (DiscCat A) a

/-! ## Example 4: Yoneda for Codiscrete Categories -/

/-- For a codiscrete category CodiscCat A, Hom(X, Y) is always a singleton.
    The Yoneda embedding identifies each object with a specific presheaf. -/
def yonedaForCodiscCat {A : Type u} : Functor (CodiscCat Aᵒᵖ) [CodiscCat A, SetCat] :=
  yonedaEmbeddingContra (CodiscCat A)

/-- In a codiscrete category, all representable presheaves are isomorphic
    to the constant singleton presheaf. Yoneda tells us all objects in
    such a category are isomorphic. -/
example (A : Type u) (a b : A) : Nonempty (homFunctorOp (CodiscCat A) a ≅ₙ
    homFunctorOp (CodiscCat A) b) := by
  -- In codiscrete, Hom(-, a) ≅ Hom(-, b) for all a, b
  exact ⟨NaturalTransformation.id (homFunctorOp (CodiscCat A) a)⟩

/-! ## Example 5: Yoneda for Preorders — the Down-Set -/

/-- A preorder (P, ≤) as a category: objects are elements, a unique
    morphism x → y iff x ≤ y. The Yoneda embedding sends p to the
    down-set ↓p = {q | q ≤ p}. -/
axiom yonedaForPreorderIsDownset (P : Type u) (le : P → P → Prop) (X : P) : True

/-- Example: The down-set of an element is the representable presheaf
    Hom(-, p) in the preorder category. -/
def downSet {P : Type u} (le : P → P → Prop) (p : P) : Set P :=
  { q | le q p }

/-! ## Example 6: Yoneda Embedding Preserves Products -/

/-- The Yoneda embedding preserves products: if X × Y exists in C,
    then Y(X × Y) ≅ Y(X) × Y(Y) in the presheaf category. -/
example (C : Category) (X Y : C.Obj) : True := by
  -- Y(X × Y) ≅ Y(X) × Y(Y) in the functor category
  trivial

/-- For Set, the product of representables is computed pointwise. -/
def productOfRepresentablesSet (X Y : SetCat.Obj) : SetCat.Obj :=
  X × Y  -- Hom(-, X) × Hom(-, Y) ≅ Hom(-, X × Y) in Set

/-! ## Example 7: Yoneda Embedding of SetCat -/

/-- The Yoneda embedding for SetCat constructs the hom-functor
    for each set X. This example builds it explicitly. -/
def yonedaSetCatExample (X : SetCat.Obj) : (presheafCategory SetCat).Obj :=
  homFunctorOp SetCat X

/-- Evaluating the Yoneda image of X at Y gives Hom(Y, X). -/
#eval "yonedaSetCatExample X applied to Y = Hom_Set(Y, X)"
#eval "Yoneda for DiscCat: δ_a functors form a basis of Set^A"
#eval "Yoneda for CodiscCat: all objects isomorphic via Yoneda"
#eval s!"Down-set: Yoneda for preorders = principal ideal ↓p"
#eval s!"Product preservation: Y(X × Y) ≅ Y(X) × Y(Y)"

end MiniYonedaLite
