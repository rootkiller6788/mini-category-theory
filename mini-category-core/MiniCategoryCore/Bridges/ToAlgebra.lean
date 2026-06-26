/-
# MiniCategoryCore.Bridges.ToAlgebra

Bridge from category theory to algebra:
monoids, groups, and rings as one-object categories; preadditive categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Properties.ClassificationData
import MiniCategoryCore.Morphisms.Hom

namespace MiniCategoryCore

/-! ## Monoid as One-Object Category -/

/-- Every monoid (M, *, 1) can be seen as a category with one object,
    where morphisms are elements of M and composition is multiplication. -/
theorem monoid_to_category {M : Type u} (mul : M → M → M) (e : M)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a) : Category :=
  MonoidCat M mul e assoc_ax id_left id_right

/-- The delooping B*M of a monoid M is the one-object category. -/
def Delooping (M : Type u) (mul : M → M → M) (e : M)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a) : Category :=
  MonoidCat M mul e assoc_ax id_left id_right

/-- Morphisms in the delooping correspond to monoid elements. -/
example {M : Type u} {mul : M → M → M} {e : M}
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a) :
    (Delooping M mul e assoc_ax id_left id_right)[(), ()] := e

/-! ## Group as One-Object Groupoid -/

/-- Every group (G, *, 1, ⁻¹) gives a one-object groupoid. -/
theorem group_to_groupoid {G : Type u} (mul : G → G → G) (e : G) (inv : G → G)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a)
    (inv_left : ∀ a, mul (inv a) a = e) (inv_right : ∀ a, mul a (inv a) = e) :
    Category ∧ isGroupoid (GroupCat G mul e inv assoc_ax id_left id_right inv_left inv_right) := by
  let C := GroupCat G mul e inv assoc_ax id_left id_right inv_left inv_right
  refine ⟨C, group_cat_is_groupoid G mul e inv assoc_ax id_left id_right inv_left inv_right⟩

/-- The delooping of a group is a connected groupoid. -/
theorem group_delooping_connected {G : Type u} (mul : G → G → G) (e : G) (inv : G → G)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a)
    (inv_left : ∀ a, mul (inv a) a = e) (inv_right : ∀ a, mul a (inv a) = e) :
    isConnected (GroupCat G mul e inv assoc_ax id_left id_right inv_left inv_right) := by
  intro X Y
  apply ZigZag.nil

/-! ## Ring as Preadditive One-Object Category -/

/-- A ring can be viewed as a preadditive category with one object.
    The additive group provides the enrichment over Ab. -/
structure RingStruct where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier
  neg : carrier → carrier
  mul : carrier → carrier → carrier
  one : carrier
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_id : ∀ a, add a zero = a
  add_inv : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_id : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

/-- The one-object preadditive category from a ring: morphisms are ring elements,
    composition is multiplication, and the additive structure is on hom-sets. -/
def RingToOneObjCat (R : RingStruct) : Category :=
  MonoidCat R.carrier R.mul R.one R.mul_assoc R.one_mul R.mul_id

#eval "Bridges.ToAlgebra: monoids, groups, rings as one-object categories"
#eval "Every monoid is a one-object category"
#eval "Every group is a one-object groupoid"
end MiniCategoryCore
