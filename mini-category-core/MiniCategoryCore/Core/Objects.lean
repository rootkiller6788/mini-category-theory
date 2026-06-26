/-
# MiniCategoryCore.Core.Objects

Registers category-theoretic types with the kernel's `Object` typeclass.
Also defines isomorphisms in a category: `IsIso`, `Iso`, and their properties.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniCategoryCore.Core.Basic

namespace MiniCategoryCore

open MiniObjectKernel

/-! ## Theory Names -/

def catTheory : Objects.TheoryName := Objects.TheoryName.ofString "CategoryTheory"

def catTheoryCore : Objects.TheoryName := catTheory.extend "Core"
def catTheoryFunctors : Objects.TheoryName := catTheory.extend "Functors"
def catTheoryAdjunctions : Objects.TheoryName := catTheory.extend "Adjunctions"

/-! ## Object Instances -/

instance : Objects.Object Category where
  theory := catTheory
  objName := "Category"
  repr _ := "𝒞"

/-! ## Small Category tag -/

inductive Size where
  | small
  | large
  deriving Repr, DecidableEq

structure SizedCategory where
  cat : Category
  size : Size

/-! ## Theory Registration -/

def theoryNode : Dependency.TheoryNode :=
  Dependency.TheoryNode.simple catTheory
    "Category Theory" "0.1.0" "2. mini-category-theory"

def dependencyEdges : List Dependency.Edge := [
  { from := catTheory, to := Objects.TheoryName.ofString "MiniMathKernel", label := "imports" }
]

/-! ## Isomorphisms -/

/-- A morphism `f : X → Y` is an isomorphism if it has a two-sided inverse. -/
def IsIso {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  ∃ (g : C[Y, X]), f ∘ g = C.id Y ∧ g ∘ f = C.id X

/-- The type of isomorphisms from `X` to `Y` in category `C`. -/
structure Iso (C : Category) (X Y : C.Obj) where
  hom : C[X, Y]
  inv : C[Y, X]
  hom_inv_id : hom ∘ inv = C.id Y
  inv_hom_id : inv ∘ hom = C.id X

/-- Extract the inverse morphism from an isomorphism. -/
def Iso.inverse {C : Category} {X Y : C.Obj} (i : Iso C X Y) : C[Y, X] := i.inv

/-- The identity isomorphism `id_X : X ≅ X`. -/
def iso_refl (C : Category) (X : C.Obj) : Iso C X X where
  hom := C.id X
  inv := C.id X
  hom_inv_id := C.comp_id (C.id X)
  inv_hom_id := C.comp_id (C.id X)

/-- The inverse (symmetry) of an isomorphism. -/
def iso_symm {C : Category} {X Y : C.Obj} (i : Iso C X Y) : Iso C Y X where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.inv_hom_id
  inv_hom_id := i.hom_inv_id

/-- Composition (transitivity) of isomorphisms. -/
def iso_trans {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (j : Iso C Y Z) : Iso C X Z where
  hom := j.hom ∘ i.hom
  inv := i.inv ∘ j.inv
  hom_inv_id := by
    calc
      (j.hom ∘ i.hom) ∘ (i.inv ∘ j.inv) = j.hom ∘ (i.hom ∘ (i.inv ∘ j.inv)) := by
        rw [← C.assoc]
      _ = j.hom ∘ ((i.hom ∘ i.inv) ∘ j.inv) := by rw [← C.assoc]
      _ = j.hom ∘ (C.id Y ∘ j.inv) := by rw [i.hom_inv_id]
      _ = j.hom ∘ j.inv := by rw [C.id_comp]
      _ = C.id Z := j.hom_inv_id
  inv_hom_id := by
    calc
      (i.inv ∘ j.inv) ∘ (j.hom ∘ i.hom) = i.inv ∘ (j.inv ∘ (j.hom ∘ i.hom)) := by
        rw [← C.assoc]
      _ = i.inv ∘ ((j.inv ∘ j.hom) ∘ i.hom) := by rw [← C.assoc]
      _ = i.inv ∘ (C.id Y ∘ i.hom) := by rw [j.inv_hom_id]
      _ = i.inv ∘ i.hom := by rw [C.id_comp]
      _ = C.id X := i.inv_hom_id

/-- Notation for isomorphism hom morphism. -/
notation i "⟶" => Iso.hom i

/-- Given a morphism and a proof it is iso, produce an `Iso`. -/
def mkIso {C : Category} {X Y : C.Obj} (f : C[X, Y]) (h : IsIso f) : Iso C X Y :=
  let ⟨g, hfg, hgf⟩ := h
  { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }

/-! ## Concrete Isomorphisms in SetCat -/

/-- In SetCat, a function is an iso iff it is a bijection. -/
def SetCat.iso_of_bijection {X Y : Type u} (f : X → Y) (g : Y → X)
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x) : Iso SetCat X Y where
  hom := f
  inv := g
  hom_inv_id := by
    ext y; apply hfg
  inv_hom_id := by
    ext x; apply hgf

/-- The swap isomorphism `Bool ≅ Bool` exchanging `true` and `false`. -/
def boolSwapIso : Iso SetCat Bool Bool :=
  SetCat.iso_of_bijection
    (λ b => !b) (λ b => !b)
    (λ b => by simp)
    (λ b => by simp)

/-- `Unit × Bool ≅ Bool`. -/
def unitProdBoolIso : Iso SetCat (Unit × Bool) Bool :=
  SetCat.iso_of_bijection
    (λ ⟨_, b⟩ => b) (λ b => ((), b))
    (λ _ => rfl) (λ _ => rfl)

#eval "Core.Objects: CategoryTheory theory, Iso, iso_refl/symm/trans, concrete SetCat isos"
#eval s!"boolSwapIso.hom true = {!true}"
#eval s!"boolSwapIso.inv false = {true}"
end MiniCategoryCore
