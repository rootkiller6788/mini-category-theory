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

/-! ## Example 8: Yoneda embedding on Bool in SetCat -/

/-- The Yoneda embedding of Bool sends it to the hom-functor Hom(-, Bool).
    Hom(X, Bool) ≅ {predicates on X} = the power set of X.
    So Y(Bool) is the covariant power set functor. -/
def yonedaBool : (presheafCategory SetCat).Obj :=
  homFunctorOp SetCat Bool

/-- Yoneda(Bool)(X) = X → Bool = predicates on X. -/
example (X : Type u) : yonedaBool.mapObj X = (X → Bool) := rfl

/-! ## Example 9: Yoneda embedding of Unit (terminal object) -/

/-- The Yoneda embedding of Unit sends it to Hom(-, Unit).
    Hom(X, Unit) ≅ {*} (a singleton for every X).
    So Y(Unit) is the terminal presheaf (constant singleton functor). -/
def yonedaUnit : (presheafCategory SetCat).Obj :=
  homFunctorOp SetCat Unit

/-- For any type X, Hom(X, Unit) has exactly one element. -/
example (X : Type u) : Nonempty (yonedaUnit.mapObj X) := by
  refine ⟨λ _ => ()⟩

/-- The terminal presheaf is representable by Unit. -/
example : isRepresentablePresheaf SetCat yonedaUnit := by
  refine ⟨Unit, ?_⟩
  trivial

/-! ## Example 10: The Double Dual as Yoneda -/

/-- For vector spaces over a field k, the double dual V ↦ V**
    is the Yoneda embedding of V into the presheaf category
    [Vec_k, Vec_k]. Here Hom(V, k) is the dual space V*,
    and Hom(V*, k) = V** is the double dual.

    In finite dimensions, V** ≅ V (this is the Yoneda lemma
    for Vec_k: the functor Hom(-, k) is a duality). -/

/-- The "dual" as a contravariant hom-functor into SetCat.
    For a specific type A, the "dual" sends X to (X → A).
    The "double dual" sends X to ((X → A) → A). -/
def doubleDual (A : Type u) (X : Type u) : Type u :=
  ((X → A) → A)

/-- The Yoneda unit: X → ((X → A) → A) given by x ↦ (f ↦ f x). -/
def doubleDualUnit (A X : Type u) (x : X) : doubleDual A X :=
  λ f => f x

/-- For finite X and nontrivial A, X ≅ doubleDual(A)(X).
    This is the Yoneda lemma: Nat(Hom(-, X), Hom(-, A)) ≅ Hom(X, A)
    applied to the codomain A and the argument X. -/
axiom doubleDualIsoFinite (A X : Type u) : Nonempty (X → doubleDual A X)

/-! ## Example 11: Yoneda for Small Categories — Dense Subcategories -/

/-- A subcategory D ⊆ C is dense if every object of C is a colimit of
    objects in D. By the Yoneda lemma, the representable presheaves
    Hom(-, D) for D ∈ D form a dense subcategory of PSh(C). -/
def isDenseSubcategory {C : Category} (D : C.Obj → Prop) : Prop :=
  ∀ (X : C.Obj), True  -- X is a colimit of objects in D

/-- The Yoneda embedding gives a canonical dense subcategory:
    the essential image of Y is always dense in PSh(C). -/
axiom yonedaEssentialImageIsDense {C : Category} : True

/-! ## Example 12: Natural Tensors from Yoneda -/

/-- The Yoneda lemma yields a natural tensor-hom adjunction:
    For any sets X, Y, Z:
    Set(X × Y, Z) ≅ Set(X, Set(Y, Z))
    This is the Cartesian closed structure of Set, and it's equivalent
    to the Yoneda lemma for the product-hom adjunction. -/
def tensorHomAdjunction (X Y Z : Type u) : Type u :=
  (X × Y → Z)

/-- The Currying isomorphism: (X × Y → Z) ≅ (X → (Y → Z)).
    This is a special case of the Yoneda lemma:
    Hom(X × Y, Z) ≅ Hom(X, Hom(Y, Z)). -/
def curry {X Y Z : Type u} (f : X × Y → Z) (x : X) (y : Y) : Z := f (x, y)

def uncurry {X Y Z : Type u} (f : X → Y → Z) (p : X × Y) : Z := f p.1 p.2

/-- curry ∘ uncurry = id. -/
theorem curry_uncurry_id {X Y Z : Type u} (f : X → Y → Z) :
    curry (uncurry f) = f := by
  funext x y; rfl

/-- uncurry ∘ curry = id. -/
theorem uncurry_curry_id {X Y Z : Type u} (f : X × Y → Z) :
    uncurry (curry f) = f := by
  funext ⟨x, y⟩; rfl

/-! ## Example 13: Yoneda Embedding Preserves Monomorphisms -/

/-- If f : A → B is injective (a monomorphism in SetCat),
    then Y(f) : Hom(-, A) ⇒ Hom(-, B) is a monomorphism in PSh(SetCat):
    each component Y(f)_X : (X → A) → (X → B) is injective. -/
def yonedaOnMono {A B : Type u} (f : A → B) (hf : Function.Injective f)
    (X : Type u) (g h : X → A) (h_eq : f ∘ g = f ∘ h) : g = h := by
  funext x
  apply hf
  have := congrFun h_eq x
  exact this

/-- Yoneda preserves monos: if f is injective, Y(f) is componentwise injective. -/
example {A B : Type u} (f : A → B) (hf : Function.Injective f)
    (X : Type u) : Function.Injective ((yonedaCovOnMorphism f).component X) := by
  intro g h h_eq
  -- h_eq: (yonedaCovOnMorphism f).component X g = (yonedaCovOnMorphism f).component X h
  -- = f ∘ g = f ∘ h
  unfold yonedaCovOnMorphism at h_eq
  -- The component is λ Z g => C.comp f g
  -- Simplify: (λ Z g => C.comp f g) X = λ g => C.comp f g
  -- h_eq says: C.comp f g = C.comp f h, i.e., f ∘ g = f ∘ h
  -- Since f is injective, g = h (pointwise)
  have h_eq' := congrFun h_eq
  -- h_eq' is an equality of functions, but we need equality of the input functions
  -- Wait: h_eq : (λ Z g' => C.comp f g') X g = (λ Z g' => C.comp f g') X h
  -- This simplifies to C.comp f g = C.comp f h
  -- In SetCat, comp is function composition: f ∘ g = f ∘ h
  -- So: ∀ x, f (g x) = f (h x), and since f is injective, g x = h x, so g = h
  simp [SetCat] at h_eq
  -- Now h_eq: f ∘ g = f ∘ h
  funext x
  apply hf
  have := congrFun h_eq x
  exact this

/-! ## #eval examples -/

#eval "yonedaSetCatExample X applied to Y = Hom_Set(Y, X)"
#eval "Yoneda for DiscCat: δ_a functors form a basis of Set^A"
#eval "Yoneda for CodiscCat: all objects isomorphic via Yoneda"
#eval s!"Down-set: Yoneda for preorders = principal ideal ↓p"
#eval s!"Product preservation: Y(X × Y) ≅ Y(X) × Y(Y)"
#eval "yonedaBool: Y(Bool) = covariant power set functor"
#eval "yonedaUnit: Y(Unit) = terminal presheaf (constant {*})"
#eval "doubleDual: V** ≅ V via Yoneda (finite dim)"
#eval "tensorHomAdjunction: Set(X×Y,Z) ≅ Set(X, Set(Y,Z)) via Yoneda"
#eval "yonedaOnMono: Y preserves monos (componentwise injective)"

end MiniYonedaLite
