/-
# MiniCategoryCore.Properties.ClassificationData

Category classification data: constructions showing how other mathematical
structures embed as categories (discrete, codiscrete, posets, monoids, groups).
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Properties.Invariants

namespace MiniCategoryCore

/-! ## Discrete Category (already in Basic, re-summarize) -/

/-- DiscCat A is discrete: the only morphisms are identities (equalities). -/
theorem discrete_category_only_ids {A : Type u} {X Y : A} (f : (DiscCat A)[X, Y]) :
    X = Y := by
  let ULift.up (PLift.up heq) := f
  exact heq

/-- Discrete categories are exactly the categories where Hom X Y is a subsingleton
    and is inhabited only when X = Y. -/
theorem discrete_category_hom_subsingleton {A : Type u} {X Y : A}
    (f g : (DiscCat A)[X, Y]) : f = g := by
  cases f; cases g; rfl

/-! ## Codiscrete Category (already in Basic, re-summarize) -/

/-- CodiscCat A is codiscrete: exactly one morphism between any two objects. -/
theorem codiscrete_unique_morphism {A : Type u} {X Y : A} (f g : (CodiscCat A)[X, Y]) : f = g := by
  cases f; cases g; rfl

/-! ## Poset as a Category -/

/-- A poset `(A, ≤)` gives a thin category with a unique morphism `X → Y` iff `X ≤ Y`. -/
def PreorderCat (A : Type u) (R : A → A → Prop) [DecidableRel R] (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c) : Category where
  Obj := A
  Hom X Y := ULift (PLift (R X Y))
  id X := ULift.up (PLift.up (refl X))
  comp g f := ULift.up (PLift.up
    (trans (PLift.down (ULift.down f)) (PLift.down (ULift.down g))))
  comp_id f := by
    cases f; cases down; cases down; rfl
  id_comp f := by
    cases f; cases down; cases down; rfl
  assoc f g h := by
    cases f; cases down; cases down
    cases g; cases down; cases down
    cases h; cases down; cases down; rfl

/-- The natural numbers with ≤ as a preorder category. -/
def NatLeCat : Category :=
  PreorderCat Nat (λ a b => a ≤ b)
    (λ a => Nat.le_refl a)
    (λ h1 h2 => Nat.le_trans h1 h2)

/-- A poset category is thin (at most one morphism per hom-set). -/
theorem preorder_cat_is_thin {A : Type u} {R : A → A → Prop} [DecidableRel R]
    {refl : ∀ a, R a a} {trans : ∀ {a b c}, R a b → R b c → R a c}
    {X Y : A} (f g : (PreorderCat A R refl trans)[X, Y]) : f = g := by
  cases f; cases g; rfl

/-! ## Monoid as a One-Object Category -/

/-- A monoid (M, *, e) can be viewed as a category with one object. -/
def MonoidCat (M : Type u) (mul : M → M → M) (e : M) (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a) : Category where
  Obj := Unit
  Hom _ _ := M
  id _ := e
  comp g f := mul g f
  comp_id f := id_right f
  id_comp f := id_left f
  assoc f g h := assoc_ax h g f

/-- The multiplicative monoid of natural numbers as a one-object category. -/
def NatMultCat : Category :=
  MonoidCat Nat Nat.mul 1
    (λ a b c => by ring)
    (λ a => by simp)
    (λ a => by simp)

/-- A group can be viewed as a one-object groupoid (every morphism is iso). -/
def GroupCat (G : Type u) (mul : G → G → G) (e : G) (inv : G → G)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a)
    (inv_left : ∀ a, mul (inv a) a = e) (inv_right : ∀ a, mul a (inv a) = e) : Category :=
  MonoidCat G mul e assoc_ax id_left id_right

/-- In a one-object group category, every morphism is an iso. -/
theorem group_cat_is_groupoid (G : Type u) (mul : G → G → G) (e : G) (inv : G → G)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a)
    (inv_left : ∀ a, mul (inv a) a = e) (inv_right : ∀ a, mul a (inv a) = e) :
    isGroupoid (GroupCat G mul e inv assoc_ax id_left id_right inv_left inv_right) := by
  intro X Y g
  exists inv g
  refine ⟨?_, ?_⟩
  · -- mul g (inv g) = e
    exact inv_right g
  · -- mul (inv g) g = e
    exact inv_left g

#eval "Properties.ClassificationData: PreorderCat, MonoidCat, GroupCat, one-object categories"
#eval s!"NatLeCat objects are natural numbers"
#eval "NatMultCat has one object (Unit)"
end MiniCategoryCore
