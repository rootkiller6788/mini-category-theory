/-
# MiniCategoryCore.Examples.Standard

Standard examples of categories: SetCat, Cat (category of categories),
Grp (groups), Top (topological spaces), Preorder and Monoid as categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Morphisms.Equivalence
import MiniCategoryCore.Properties.ClassificationData
import MiniCategoryCore.Theorems.Basic
import MiniCategoryCore.Constructions.Universal

namespace MiniCategoryCore

/-! ## SetCat: Category of Types and Functions -/

/-- SetCat example: the identity function on Nat is a morphism. -/
example : SetCat[Nat, Nat] := SetCat.id Nat

/-- SetCat example: the successor function. -/
def succMorphism : SetCat[Nat, Nat] := Nat.succ

/-- In SetCat, composition is function composition. -/
example : (SetCat.comp (λ n : Nat => n + 1) (λ n : Nat => n * 2)) 3 = 7 := rfl

/-- SetCat has initial object Empty and terminal object Unit
    (defined in Constructions/Universal.lean). Use `SetCat.initial` and `SetCat.terminal`. -/
example : SetCat[Empty, Unit] := SetCat.initial.initiate Unit
example : SetCat[Unit, Empty] := SetCat.terminal.terminate Empty

/-! ## Cat: The Category of Categories -/

/-- Categories form a (large) category with functors as morphisms. -/
def CatCat : Category where
  Obj := Category
  Hom C D := Functor C D
  id C := Functor.idF C
  comp G F := G ∘ᶠ F
  comp_id F := by
    apply Functor.ext
    · intro X; rfl
    · intro X Y f; rfl
  id_comp F := by
    apply Functor.ext
    · intro X; rfl
    · intro X Y f; rfl
  assoc H G F := by
    apply Functor.ext
    · intro X; rfl
    · intro X Y f; rfl

/-- The identity functor on SetCat is an object of CatCat. -/
def CatCat.example : CatCat := Functor.idF SetCat

/-! ## Grp: Category of Groups (Skeletal) -/

/-- A group is a type with multiplication, identity, and inverses. -/
structure Group where
  carrier : Type u
  mul : carrier → carrier → carrier
  e : carrier
  inv : carrier → carrier
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  id_left : ∀ a, mul e a = a
  id_right : ∀ a, mul a e = a
  inv_left : ∀ a, mul (inv a) a = e
  inv_right : ∀ a, mul a (inv a) = e

/-- A group homomorphism. -/
structure GroupHom (G H : Group) where
  map : G.carrier → H.carrier
  mul_preserves : ∀ a b, map (G.mul a b) = H.mul (map a) (map b)

/-- The category of groups (conceptual; full definition requires grouping/universe management). -/
def GrpCat : Category where
  Obj := Group
  Hom G H := GroupHom G H
  id G := { map := λ x => x, mul_preserves := λ _ _ => rfl }
  comp h g := {
    map := h.map ∘ g.map,
    mul_preserves := by
      intro a b
      simp [h.mul_preserves, g.mul_preserves]
  }
  comp_id h := by
    ext x; rfl
  id_comp h := by
    ext x; rfl
  assoc h g f := by
    ext x; rfl

/-! ## Top: Category of Topological Spaces -/

/-- A topological space is a type with a designated collection of open sets.
    Here we provide a conceptual placeholder. -/
structure TopSpace where
  carrier : Type u
  opens : carrier → Prop
  -- In a full definition: opens would be Set (Set carrier) with closure properties

/-- A continuous map between topological spaces. -/
structure ContinuousMap (X Y : TopSpace) where
  map : X.carrier → Y.carrier
  -- In a full definition: preimage of open is open

/-- The category of topological spaces (conceptual placeholder). -/
axiom TopCat : Category

/-! ## Preorder as Category (already in ClassificationData) -/

/-- A preorder (A, ≤) forms a thin category. -/
example : Category := PreorderCat Nat (λ a b => a ≤ b) Nat.le_refl
  (λ h1 h2 => Nat.le_trans h1 h2)

/-- In a preorder category, there is at most one morphism per hom-set. -/
example (a b : Nat) (f g : (PreorderCat Nat (λ x y => x ≤ y) Nat.le_refl
    (λ h1 h2 => Nat.le_trans h1 h2))[a, b]) : f = g := by
  cases f; cases g; rfl

/-! ## Monoid as One-Object Category -/

/-- The natural numbers under addition form a monoid, hence a one-object category. -/
def NatAddMonoid : Category :=
  MonoidCat Nat Nat.add 0
    (λ a b c => by ring)
    (λ a => Nat.zero_add a)
    (λ a => Nat.add_zero a)

/-- In NatAddMonoid, the morphisms are natural numbers, composition is addition. -/
example : NatAddMonoid[(), ()] := (3 : Nat)

#eval "Examples.Standard: SetCat, CatCat, GrpCat, TopCat, PreorderCat, MonoidCat"
#eval s!"SetCat has initial object Empty: True"
#eval s!"CatCat: the category of categories has categories as objects"
#eval "NatAddMonoid: one-object category where morphisms are natural numbers under addition"
end MiniCategoryCore
