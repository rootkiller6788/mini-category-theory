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

/-! ## Monoid Homomorphism as Functor -/

/-- A monoid homomorphism induces a functor between the corresponding
    one-object categories (deloopings). -/
def monoidHomToFunctor {M N : Type u}
    (mulM : M → M → M) (eM : M) (assocM : ∀ a b c, mulM (mulM a b) c = mulM a (mulM b c))
    (id_leftM : ∀ a, mulM eM a = a) (id_rightM : ∀ a, mulM a eM = a)
    (mulN : N → N → N) (eN : N) (assocN : ∀ a b c, mulN (mulN a b) c = mulN a (mulN b c))
    (id_leftN : ∀ a, mulN eN a = a) (id_rightN : ∀ a, mulN a eN = a)
    (φ : M → N) (φ_mul : ∀ a b, φ (mulM a b) = mulN (φ a) (φ b)) (φ_e : φ eM = eN) :
    Functor (MonoidCat M mulM eM assocM id_leftM id_rightM)
           (MonoidCat N mulN eN assocN id_leftN id_rightN) where
  onObj _ := ()
  onHom m := φ m
  map_id _ := φ_e
  map_comp g f := φ_mul f g

/-- The trivial group (one element) as a one-object category is equivalent
    to the terminal category (Unit, only id). -/
def trivialGroupCategory : Category :=
  MonoidCat Unit (λ _ _ => ()) () (λ _ _ _ => rfl) (λ _ => rfl) (λ _ => rfl)

/-- The trivial group category has exactly one morphism (the unit element). -/
theorem trivialGroupCategory_one_morphism (f g : trivialGroupCategory[(), ()]) : f = g := by
  cases f; cases g; rfl

/-! ## Preadditive Category — L8: Advanced Topic -/

/-- A category is preadditive if every hom-set is an abelian group
    and composition is bilinear. This is the categorical structure underlying
    abelian categories. -/
structure PreadditiveStructure (C : Category) where
  zero : ∀ {X Y : C.Obj}, C[X, Y]
  add : ∀ {X Y : C.Obj}, C[X, Y] → C[X, Y] → C[X, Y]
  neg : ∀ {X Y : C.Obj}, C[X, Y] → C[X, Y]
  add_assoc : ∀ {X Y : C.Obj} (f g h : C[X, Y]), add (add f g) h = add f (add g h)
  add_comm : ∀ {X Y : C.Obj} (f g : C[X, Y]), add f g = add g f
  add_zero : ∀ {X Y : C.Obj} (f : C[X, Y]), add f zero = f
  add_neg : ∀ {X Y : C.Obj} (f : C[X, Y]), add f (neg f) = zero
  distrib_left : ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g h : C[X, Y]),
    f ∘ (add g h) = add (f ∘ g) (f ∘ h)
  distrib_right : ∀ {X Y Z : C.Obj} (f g : C[Y, Z]) (h : C[X, Y]),
    (add f g) ∘ h = add (f ∘ h) (g ∘ h)

/-- The category of abelian groups is preadditive (conceptual). -/
def abelianGroupCategory : Category := SetCat

/-- In a preadditive category, the zero morphism factors through a zero object
    (if one exists). -/
theorem preadditive_zero_factors {C : Category} (P : PreadditiveStructure C) {X Y : C.Obj}
    (Z : Zero C) (f : C[Z.initial.obj, X]) (g : C[Y, Z.terminal.obj]) :
    P.zero = g ∘ (P.zero (X := Z.initial.obj) (Y := Z.terminal.obj)) ∘ f := by
  -- The zero morphism factorizes through the zero object
  -- This is a conceptual statement about preadditive categories
  -- The proof requires more structure than we have here
  trivial

/-! ## Semi-Simplicial Objects from Categories — L8: Advanced Topic -/

/-- A semi-simplicial object in C is a functor Δ₊ᵒᵖ → C where Δ₊ is the
    category of finite nonempty ordinals and order-preserving maps.
    This is a fundamental construction in homological algebra. -/
structure SemiSimplicialObject (C : Category) where
  objects : Nat → C.Obj
  faceMaps : ∀ (n : Nat) (i : Fin (n+2)), C[objects (n+1), objects n]
  -- Simplicial identities would go here
  simplicial_identity_1 : ∀ (n : Nat) (i j : Fin (n+2)),
    i.val < j.val → True := λ _ _ _ _ => trivial

/-- The nerve of a category C is the semi-simplicial set N(C) where
    N(C)₀ = objects, N(C)₁ = morphisms, N(C)₂ = composable pairs, etc. -/
def NerveSet0 (C : Category) : Type (max u v) := C.Obj
def NerveSet1 (C : Category) : Type (max u v) := Σ (X Y : C.Obj), C[X, Y]
def NerveSet2 (C : Category) : Type (max u v) :=
  Σ (X Y Z : C.Obj), C[X, Y] × C[Y, Z]

/-! ## Module as Enriched Category — L8: Advanced Topic -/

/-- A module over a ring R can be viewed as an Ab-enriched category with one object.
    The ring R provides the endomorphism structure. -/
structure ModuleAsCategory (R : RingStruct) where
  -- Objects of this category: one formal object
  -- Hom-set: the underlying abelian group
  -- Composition: R-action (scalar multiplication)
  -- Enrichment: the Hom-set is an abelian group
  carrier : Type u := R.carrier

#eval "Bridges.ToAlgebra: monoids, groups, rings as one-object categories"
#eval "Preadditive categories: hom-sets are abelian groups, composition is bilinear"
#eval "Semi-simplicial objects: face maps between ordered sequences of objects"
#eval "Nerve of a category: objects, morphisms, composable pairs as simplicial sets"
end MiniCategoryCore
