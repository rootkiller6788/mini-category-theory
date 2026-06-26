/-
# MiniCategoryCore.Core.Laws

Category-theoretic axioms encoded as kernel `Axiom` values.
Also theorems about isomorphisms: equivalence relation, composition, preservation.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects
import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

open MiniObjectKernel

/-! ## Category Axioms as Propositions -/

def associativityLaw (C : Category) : Prop :=
  ∀ {W X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]) (h : C[W, X]),
    C.comp f (C.comp g h) = C.comp (C.comp f g) h

def leftIdentityLaw (C : Category) : Prop :=
  ∀ {X Y : C.Obj} (f : C[X, Y]), C.comp (C.id Y) f = f

def rightIdentityLaw (C : Category) : Prop :=
  ∀ {X Y : C.Obj} (f : C[X, Y]), C.comp f (C.id X) = f

theorem categoryLaws (C : Category) :
    associativityLaw C ∧ leftIdentityLaw C ∧ rightIdentityLaw C := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ _ f g h; exact C.assoc f g h
  · intro _ _ f; exact C.id_comp f
  · intro _ _ f; exact C.comp_id f

/-! ## Functor Laws -/

def preservesId {C D : Category} (mapObj : C.Obj → D.Obj)
    (mapHom : ∀ {X Y : C.Obj}, C[X, Y] → D[mapObj X, mapObj Y]) : Prop :=
  ∀ (X : C.Obj), mapHom (C.id X) = D.id (mapObj X)

def preservesComp {C D : Category} (mapObj : C.Obj → D.Obj)
    (mapHom : ∀ {X Y : C.Obj}, C[X, Y] → D[mapObj X, mapObj Y]) : Prop :=
  ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]),
    mapHom (C.comp f g) = D.comp (mapHom f) (mapHom g)

/-! ## Natural Transformation Laws -/

def naturalitySquare {C D : Category}
    (F G : C.Obj → D.Obj)
    (mapF : ∀ {X Y : C.Obj}, C[X, Y] → D[F X, F Y])
    (mapG : ∀ {X Y : C.Obj}, C[X, Y] → D[G X, G Y])
    (component : ∀ (X : C.Obj), D[F X, G X]) : Prop :=
  ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (mapF f) = D.comp (mapG f) (component X)

/-! ## Axiom System for Category Theory -/

def catAxioms : Axioms.AxiomSet :=
  Axioms.AxiomSet.empty
    |>.add (Axioms.Axiom.described "cat-associativity" (Formula.atom 0)
      "Composition is associative: f ∘ (g ∘ h) = (f ∘ g) ∘ h")
    |>.add (Axioms.Axiom.described "cat-left-identity" (Formula.atom 1)
      "Left identity: id ∘ f = f")
    |>.add (Axioms.Axiom.described "cat-right-identity" (Formula.atom 2)
      "Right identity: f ∘ id = f")
    |>.add (Axioms.Axiom.described "functor-identity" (Formula.atom 3)
      "Functors preserve identity: F(id) = id")

def catSystem : Axioms.AxiomSystem :=
  Axioms.AxiomSystem.empty "CategoryTheory" "0.1.0"
    |>.addAxioms catAxioms.axioms

/-! ## Isomorphism Laws -/

/-- Isomorphisms form an equivalence relation on objects. -/
theorem iso_is_equiv_rel (C : Category) :
    (∀ X : C.Obj, Iso C X X) ∧
    (∀ {X Y : C.Obj}, Iso C X Y → Iso C Y X) ∧
    (∀ {X Y Z : C.Obj}, Iso C X Y → Iso C Y Z → Iso C X Z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X; exact iso_refl C X
  · intro X Y i; exact iso_symm i
  · intro X Y Z i j; exact iso_trans i j

/-- The identity morphism is an isomorphism. -/
theorem id_is_iso (C : Category) (X : C.Obj) : IsIso (C.id X) := by
  exists C.id X
  refine ⟨?_, ?_⟩
  · exact C.comp_id (C.id X)
  · exact C.comp_id (C.id X)

/-- Composition of isomorphisms yields an isomorphism. -/
theorem comp_iso {C : Category} {X Y Z : C.Obj}
    (f : C[X, Y]) (g : C[Y, Z]) (hf : IsIso f) (hg : IsIso g) : IsIso (g ∘ f) := by
  rcases hf with ⟨f_inv, hf1, hf2⟩
  rcases hg with ⟨g_inv, hg1, hg2⟩
  exists f_inv ∘ g_inv
  refine ⟨?_, ?_⟩
  · calc
      (g ∘ f) ∘ (f_inv ∘ g_inv) = g ∘ (f ∘ (f_inv ∘ g_inv)) := by rw [← C.assoc]
      _ = g ∘ ((f ∘ f_inv) ∘ g_inv) := by rw [← C.assoc]
      _ = g ∘ (C.id Y ∘ g_inv) := by rw [hf1]
      _ = g ∘ g_inv := by rw [C.id_comp]
      _ = C.id Z := hg1
  · calc
      (f_inv ∘ g_inv) ∘ (g ∘ f) = f_inv ∘ (g_inv ∘ (g ∘ f)) := by rw [← C.assoc]
      _ = f_inv ∘ ((g_inv ∘ g) ∘ f) := by rw [← C.assoc]
      _ = f_inv ∘ (C.id Y ∘ f) := by rw [hg2]
      _ = f_inv ∘ f := by rw [C.id_comp]
      _ = C.id X := hf2

/-- If f is iso, then composing with f on either side preserves iso property. -/
theorem iso_preserves_properties {C : Category} {X Y Z W : C.Obj}
    (f : C[X, Y]) (g : C[Y, Z]) (h : C[Z, W])
    (hf : IsIso f) (hg : IsIso g) (hh : IsIso h) :
    IsIso (h ∘ g ∘ f) := by
  have h_mid : IsIso (g ∘ f) := comp_iso f g hf hg
  exact comp_iso (g ∘ f) h h_mid hh

/-- A morphism `f` satisfying left and right identity laws must equal `id`. -/
theorem unique_id {C : Category} (X : C.Obj) (e : C[X, X])
    (hleft : ∀ (f : C[X, X]), e ∘ f = f)
    (hright : ∀ (f : C[X, X]), f ∘ e = f) : e = C.id X := by
  calc
    e = e ∘ C.id X := by rw [C.comp_id]
    _ = C.id X := hleft (C.id X)

#eval "Core.Laws: iso_equiv_rel, comp_iso, id_is_iso, iso_preserves, unique_id"
#eval s!"iso is an equiv relation for SetCat: {(iso_is_equiv_rel SetCat).1 Unit}"
#eval s!"id(Unit) is iso in SetCat: {id_is_iso SetCat Unit}"
end MiniCategoryCore
