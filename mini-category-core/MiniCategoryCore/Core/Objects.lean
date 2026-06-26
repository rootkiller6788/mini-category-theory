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

/-- Self-contained theory node for the category theory module. -/
structure CatTheoryNode where
  name : Objects.TheoryName
  title : String
  version : String
  path : String
  deriving Repr

def theoryNode : CatTheoryNode :=
  { name := catTheory, title := "Category Theory", version := "0.1.0", path := "2. mini-category-theory" }

/-- Dependency edge from category theory to the math kernel. -/
structure CatDependencyEdge where
  source : Objects.TheoryName
  target : Objects.TheoryName
  label : String
  deriving Repr

def dependencyEdges : List CatDependencyEdge := [
  { source := catTheory, target := Objects.TheoryName.ofString "MiniMathKernel", label := "imports" }
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

/-! ## Isomorphism Properties: Equivalence Relation -/

/-- The iso relation on objects is reflexive. -/
theorem iso_refl' (C : Category) (X : C.Obj) : Nonempty (Iso C X X) :=
  ⟨iso_refl C X⟩

/-- The iso relation on objects is symmetric. -/
theorem iso_symm' {C : Category} {X Y : C.Obj} (h : Nonempty (Iso C X Y)) : Nonempty (Iso C Y X) := by
  rcases h with ⟨i⟩; exact ⟨iso_symm i⟩

/-- The iso relation on objects is transitive. -/
theorem iso_trans' {C : Category} {X Y Z : C.Obj}
    (hXY : Nonempty (Iso C X Y)) (hYZ : Nonempty (Iso C Y Z)) : Nonempty (Iso C X Z) := by
  rcases hXY with ⟨i⟩; rcases hYZ with ⟨j⟩; exact ⟨iso_trans i j⟩

/-! ## Endomorphism Monoid of an Object -/

/-- The set of endomorphisms C[X,X] forms a monoid under composition. -/
structure EndoMonoid (C : Category) (X : C.Obj) where
  endos : Type v := C[X, X]
  one : endos := C.id X
  mul : endos → endos → endos := λ f g => f ∘ g
  mul_assoc : ∀ (f g h : endos), mul (mul f g) h = mul f (mul g h) :=
    λ f g h => by unfold mul; rw [C.assoc]
  one_mul : ∀ (f : endos), mul one f = f :=
    λ f => by unfold mul one; rw [C.id_comp]
  mul_one : ∀ (f : endos), mul f one = f :=
    λ f => by unfold mul one; rw [C.comp_id]

/-- The automorphism group Aut(X) of an object X consists of isomorphisms X ≅ X. -/
structure AutoGroup (C : Category) (X : C.Obj) where
  autos : Type v := C[X, X]
  membership : autos → Prop := IsIso
  id_mem : membership (C.id X) := by
    exists C.id X
    refine ⟨C.comp_id _, C.comp_id _⟩
  comp_mem : ∀ {f g : autos}, membership f → membership g → membership (f ∘ g) :=
    λ f g hf hg => comp_iso f g hf hg
  inv_mem : ∀ {f : autos}, membership f → membership (Iso.inv (mkIso f (by
    rcases membership f with h; exact h))) := by
    intro f hf
    let i := mkIso f hf
    have : Iso.inv i ∘ f = C.id X := i.inv_hom_id
    exists f
    refine ⟨C.comp_id _, this⟩

/-! ## Coherence of Iso Operations -/

/-- iso_refl composed with any iso is that iso. -/
theorem iso_refl_trans {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    iso_trans (iso_refl C X) i = i := by
  ext <;> simp [iso_refl, iso_trans, C.id_comp]

/-- Any iso composed with iso_refl is that iso. -/
theorem iso_trans_refl {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    iso_trans i (iso_refl C Y) = i := by
  ext <;> simp [iso_refl, iso_trans, C.comp_id]

/-- The double-symm cancels: iso_symm (iso_symm i) = i. -/
theorem iso_symm_symm {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    iso_symm (iso_symm i) = i := by
  ext <;> rfl

/-! ## Iso Induced by a Bijection on Hom-Sets (Reference) -/

/-- The Yoneda principle: if Hom(Z,X) ≅ Hom(Z,Y) naturally in Z, then X ≅ Y.
    This is a special case of the Yoneda lemma and is stated as a reference. -/
axiom yoneda_principle {C : Category} {X Y : C.Obj}
    (Φ : ∀ (Z : C.Obj), C[Z, X] → C[Z, Y])
    (natural : ∀ {Z W : C.Obj} (g : C[Z, W]) (f : C[W, X]),
      Φ Z (f ∘ g) = (Φ W f) ∘ g)
    (Φ_bij : ∀ (Z : C.Obj), Function.Bijective (Φ Z)) : Nonempty (Iso C X Y)

/-! ## Concrete SetCat Isomorphisms — More Examples -/

/-- The pair type `A × B` is isomorphic to `B × A` (commutativity of product). -/
def prodCommIso (A B : Type u) : Iso SetCat (A × B) (B × A) :=
  SetCat.iso_of_bijection
    (λ ⟨a, b⟩ => (b, a)) (λ ⟨b, a⟩ => (a, b))
    (λ _ => rfl) (λ _ => rfl)

/-- `Option A` is isomorphic to `A ⊕ Unit` (where ⊕ is Sum). -/
def optionIsoSumUnit (A : Type u) : Iso SetCat (Option A) (A ⊕ Unit) :=
  SetCat.iso_of_bijection
    (λ x => match x with
      | Option.some a => Sum.inl a
      | Option.none => Sum.inr ())
    (λ x => match x with
      | Sum.inl a => Option.some a
      | Sum.inr () => Option.none)
    (λ x => by cases x <;> rfl)
    (λ x => by cases x <;> rfl)

/-- `A ⊕ B` is isomorphic to `B ⊕ A` (commutativity of sum). -/
def sumCommIso (A B : Type u) : Iso SetCat (A ⊕ B) (B ⊕ A) :=
  SetCat.iso_of_bijection
    (λ x => match x with
      | Sum.inl a => Sum.inr a
      | Sum.inr b => Sum.inl b)
    (λ x => match x with
      | Sum.inl b => Sum.inr b
      | Sum.inr a => Sum.inl a)
    (λ x => by cases x <;> rfl)
    (λ x => by cases x <;> rfl)

#eval "Core.Objects: CategoryTheory theory, Iso, iso_refl/symm/trans, concrete SetCat isos"
#eval s!"boolSwapIso.hom true = {!true}"
#eval s!"boolSwapIso.inv false = {true}"
#eval s!"prodCommIso (A:=Nat) (B:=Bool) : Iso (Nat × Bool) (Bool × Nat)"
end MiniCategoryCore
