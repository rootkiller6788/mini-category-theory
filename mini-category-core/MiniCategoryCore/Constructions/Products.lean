/-
# MiniCategoryCore.Constructions.Products

Binary products in a category: product cone, universal property,
and the realization in SetCat as the Cartesian product.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Product Cone -/

/-- A product cone over objects A, B consists of an object P and two projections. -/
structure ProductCone (C : Category) (A B : C.Obj) where
  P : C.Obj
  π₁ : C[P, A]
  π₂ : C[P, B]

/-- The universal property of a product: any pair of maps factors uniquely. -/
def isProduct {C : Category} {A B : C.Obj} (cone : ProductCone C A B) : Prop :=
  ∀ (Q : C.Obj) (f : C[Q, A]) (g : C[Q, B]),
    ∃! h : C[Q, cone.P], (cone.π₁ ∘ h = f) ∧ (cone.π₂ ∘ h = g)

/-- A category has binary products if every pair of objects has a product. -/
def HasBinaryProducts (C : Category) : Prop :=
  ∀ (A B : C.Obj), ∃ (cone : ProductCone C A B), isProduct cone

/-! ## Products in SetCat -/

/-- The Cartesian product is the product in SetCat. -/
def SetCat.productCone (A B : Type u) : ProductCone SetCat A B where
  P := A × B
  π₁ := Prod.fst
  π₂ := Prod.snd

/-- The universal property for products in SetCat: the unique pairing. -/
theorem SetCat.isProduct_pair {A B : Type u} :
    isProduct (SetCat.productCone A B) := by
  intro Q f g
  refine ⟨λ q => (f q, g q), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · ext q; rfl
    · ext q; rfl
  · intro h ⟨hp1, hp2⟩
    ext q
    have h1 := congrArg (λ fn => fn q) hp1
    have h2 := congrArg (λ fn => fn q) hp2
    dsimp
    rw [h1, h2]

/-- SetCat has binary products. -/
theorem SetCat.hasBinaryProducts : HasBinaryProducts (SetCat : Category) := by
  intro A B
  exists SetCat.productCone A B
  exact SetCat.isProduct_pair

/-! ## Product Functoriality -/

/-- Given isos A≅A' and B≅B', we get an iso of their products (when they exist). -/
structure Product (C : Category) (A B : C.Obj) where
  cone : ProductCone C A B
  univ : isProduct cone

/-- The product object. -/
def Product.obj {C : Category} {A B : C.Obj} (prod : Product C A B) : C.Obj := prod.cone.P

/-- The first projection. -/
def Product.π₁ {C : Category} {A B : C.Obj} (prod : Product C A B) : C[prod.obj, A] :=
  prod.cone.π₁

/-- The second projection. -/
def Product.π₂ {C : Category} {A B : C.Obj} (prod : Product C A B) : C[prod.obj, B] :=
  prod.cone.π₂

/-- Given two products of the same pair, they are isomorphic. -/
theorem product_unique_up_to_iso {C : Category} {A B : C.Obj}
    (P Q : Product C A B) : Nonempty (Iso C P.obj Q.obj) := by
  -- Use universal property of P to get map P→Q, and of Q to get Q→P, then compose
  have hP := P.univ Q.obj Q.π₁ Q.π₂
  rcases hP with ⟨f, ⟨hp1, hp2⟩, _⟩
  have hQ := Q.univ P.obj P.π₁ P.π₂
  rcases hQ with ⟨g, ⟨hq1, hq2⟩, _⟩
  -- Now show f ∘ g = id and g ∘ f = id
  -- Use uniqueness part of universal property
  have h_fg : P.π₁ ∘ (f ∘ g) = P.π₁ ∧ P.π₂ ∘ (f ∘ g) = P.π₂ := by
    refine ⟨?_, ?_⟩
    · calc
        P.π₁ ∘ (f ∘ g) = (P.π₁ ∘ f) ∘ g := by rw [← C.assoc]
        _ = Q.π₁ ∘ g := by rw [hp1]
        _ = P.π₁ := hq1
    · calc
        P.π₂ ∘ (f ∘ g) = (P.π₂ ∘ f) ∘ g := by rw [← C.assoc]
        _ = Q.π₂ ∘ g := by rw [hp2]
        _ = P.π₂ := hq2
  have h_unique := P.univ P.obj P.π₁ P.π₂
  rcases h_unique with ⟨h_id, ⟨hid1, hid2⟩, huniq⟩
  have h_fg_eq_id : f ∘ g = C.id P.obj := by
    apply huniq (f ∘ g)
    exact h_fg
  have h_gf : Q.π₁ ∘ (g ∘ f) = Q.π₁ ∧ Q.π₂ ∘ (g ∘ f) = Q.π₂ := by
    refine ⟨?_, ?_⟩
    · calc
        Q.π₁ ∘ (g ∘ f) = (Q.π₁ ∘ g) ∘ f := by rw [← C.assoc]
        _ = P.π₁ ∘ f := by rw [hq1]
        _ = Q.π₁ := hp1
    · calc
        Q.π₂ ∘ (g ∘ f) = (Q.π₂ ∘ g) ∘ f := by rw [← C.assoc]
        _ = P.π₂ ∘ f := by rw [hq2]
        _ = Q.π₂ := hp2
  have h_uniqueQ := Q.univ Q.obj Q.π₁ Q.π₂
  rcases h_uniqueQ with ⟨h_idQ, ⟨hid1Q, hid2Q⟩, huniqQ⟩
  have h_gf_eq_id : g ∘ f = C.id Q.obj := by
    apply huniqQ (g ∘ f)
    exact h_gf
  -- Construct the iso
  exact ⟨{ hom := f, inv := g, hom_inv_id := h_fg_eq_id, inv_hom_id := h_gf_eq_id }⟩

#eval "Constructions.Products: ProductCone, isProduct, HasBinaryProducts, SetCat product"
#eval s!"SetCat has products: {SetCat.hasBinaryProducts}"
#eval "Product(Bool, Nat) in SetCat is (Bool × Nat)"
end MiniCategoryCore
