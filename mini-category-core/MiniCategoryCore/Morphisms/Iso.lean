/-
# MiniCategoryCore.Morphisms.Iso

Operations on isomorphisms: composition in the arrow category,
whiskering (pre- and post-composition with morphisms),
and naturality squares induced by isomorphisms.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Vertical and Horizontal Iso Composition -/

/-- Vertical composition of isos (same as `iso_trans`). -/
def iso_vcomp {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (j : Iso C Y Z) : Iso C X Z :=
  iso_trans i j

/-- If we have isos W≅X, X≅Y, Y≅Z then W≅Z by transitivity. -/
def iso_triple_comp {C : Category} {W X Y Z : C.Obj}
    (i : Iso C W X) (j : Iso C X Y) (k : Iso C Y Z) : Iso C W Z :=
  iso_trans (iso_trans i j) k

/-! ## Whiskering: composing an iso with a morphism -/

/-- Pre-composition with an isomorphism (whiskering on the left). -/
def whiskerLeft {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (f : C[Y, Z]) : C[X, Z] :=
  f ∘ i.hom

/-- Post-composition with an isomorphism (whiskering on the right). -/
def whiskerRight {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (i : Iso C Y Z) : C[X, Z] :=
  i.hom ∘ f

/-- Whiskering an iso with another iso gives an iso. -/
def whiskerIsoLeft {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (j : Iso C Y Z) : Iso C X Z :=
  iso_trans i j

/-- Whiskering a morphism on both sides by isos. -/
def whiskerIso {C : Category} {X Y X' Y' : C.Obj}
    (f : C[X, Y]) (i : Iso C X' X) (j : Iso C Y Y') : C[X', Y'] :=
  j.hom ∘ f ∘ i.inv

/-- The whiskered morphism is iso if the original is. -/
theorem whiskerIso_preserves_iso {C : Category} {X Y X' Y' : C.Obj}
    (f : C[X, Y]) (i : Iso C X' X) (j : Iso C Y Y') (hf : IsIso f) : IsIso (whiskerIso f i j) := by
  rcases hf with ⟨g, hfg, hgf⟩
  unfold whiskerIso
  have h_right : (j.hom ∘ f ∘ i.inv) ∘ (i.hom ∘ g ∘ j.inv) = C.id Y' := by
    calc
      (j.hom ∘ f ∘ i.inv) ∘ (i.hom ∘ g ∘ j.inv)
          = j.hom ∘ ((f ∘ i.inv) ∘ (i.hom ∘ g ∘ j.inv)) := by rw [← C.assoc]
      _ = j.hom ∘ (f ∘ (i.inv ∘ i.hom) ∘ g ∘ j.inv) := by
            rw [← C.assoc (i.inv) (i.hom ∘ g ∘ j.inv), C.assoc f i.inv (i.hom ∘ g ∘ j.inv),
              ← C.assoc (i.hom) (g ∘ j.inv), C.assoc (i.inv) i.hom (g ∘ j.inv)]
      _ = j.hom ∘ (f ∘ (C.id X) ∘ g ∘ j.inv) := by rw [i.inv_hom_id]
      _ = j.hom ∘ (f ∘ g ∘ j.inv) := by rw [C.id_comp]
      _ = j.hom ∘ ((f ∘ g) ∘ j.inv) := by rw [C.assoc]
      _ = j.hom ∘ (C.id Y ∘ j.inv) := by rw [hfg]
      _ = j.hom ∘ j.inv := by rw [C.id_comp]
      _ = C.id Y' := j.hom_inv_id
  have h_left : (i.hom ∘ g ∘ j.inv) ∘ (j.hom ∘ f ∘ i.inv) = C.id X' := by
    calc
      (i.hom ∘ g ∘ j.inv) ∘ (j.hom ∘ f ∘ i.inv)
          = i.hom ∘ ((g ∘ j.inv) ∘ (j.hom ∘ f ∘ i.inv)) := by rw [← C.assoc]
      _ = i.hom ∘ (g ∘ (j.inv ∘ j.hom) ∘ f ∘ i.inv) := by
            rw [← C.assoc (j.inv) (j.hom ∘ f ∘ i.inv), C.assoc g j.inv (j.hom ∘ f ∘ i.inv),
              ← C.assoc (j.hom) (f ∘ i.inv), C.assoc j.inv j.hom (f ∘ i.inv)]
      _ = i.hom ∘ (g ∘ (C.id Y) ∘ f ∘ i.inv) := by rw [j.inv_hom_id]
      _ = i.hom ∘ (g ∘ f ∘ i.inv) := by rw [C.id_comp]
      _ = i.hom ∘ ((g ∘ f) ∘ i.inv) := by rw [C.assoc]
      _ = i.hom ∘ (C.id X ∘ i.inv) := by rw [hgf]
      _ = i.hom ∘ i.inv := by rw [C.id_comp]
      _ = C.id X' := i.hom_inv_id
  exists (i.hom ∘ g ∘ j.inv)
  refine ⟨h_right, h_left⟩

/-! ## Iso Naturality Square -/

/-- A naturality square induced by isomorphisms:
    Given isos a : X ≅ X', b : Y ≅ Y' and f : X → Y, g : X' → Y',
    the square commutes if f ∘ a.inv = b.inv ∘ g (via the iso inverses). -/
def IsoNatSquare {C : Category} {X Y X' Y' : C.Obj}
    (a : Iso C X X') (b : Iso C Y Y')
    (f : C[X, Y]) (g : C[X', Y']) : Prop :=
  f ∘ a.inv = b.inv ∘ g

/-- Equivalent formulation: b.hom ∘ f = g ∘ a.hom. -/
theorem isoNatSquare_alt {C : Category} {X Y X' Y' : C.Obj}
    (a : Iso C X X') (b : Iso C Y Y')
    (f : C[X, Y]) (g : C[X', Y']) :
    (f ∘ a.inv = b.inv ∘ g) ↔ (b.hom ∘ f = g ∘ a.hom) := by
  constructor
  · intro h
    calc
      b.hom ∘ f = (b.hom ∘ f) ∘ (a.inv ∘ a.hom) := by rw [a.inv_hom_id, C.comp_id]
      _ = b.hom ∘ f ∘ a.inv ∘ a.hom := by rw [C.assoc]
      _ = b.hom ∘ (b.inv ∘ g) ∘ a.hom := by rw [h, C.assoc]
      _ = (b.hom ∘ b.inv) ∘ (g ∘ a.hom) := by rw [← C.assoc g a.hom, C.assoc b.hom b.inv g]
      _ = C.id Y ∘ (g ∘ a.hom) := by rw [b.hom_inv_id]
      _ = g ∘ a.hom := by rw [C.id_comp]
  · intro h
    calc
      f ∘ a.inv = (b.inv ∘ b.hom) ∘ f ∘ a.inv := by rw [b.inv_hom_id, C.id_comp]
      _ = b.inv ∘ (b.hom ∘ f) ∘ a.inv := by rw [C.assoc, C.assoc]
      _ = b.inv ∘ (g ∘ a.hom) ∘ a.inv := by rw [h]
      _ = b.inv ∘ g ∘ a.hom ∘ a.inv := by rw [← C.assoc a.hom a.inv, C.assoc b.inv g a.hom]
      _ = b.inv ∘ g ∘ (a.hom ∘ a.inv) := by rw [C.assoc]
      _ = b.inv ∘ g ∘ C.id X' := by rw [a.hom_inv_id]
      _ = b.inv ∘ g := by rw [C.comp_id]

/-! ## Iso Operations on Objects -/

/-- Type synonym representing objects up to isomorphism. -/
def IsoClass (C : Category) : Type u := C.Obj

/-- Two objects are isomorphic. -/
def AreIsomorphic (C : Category) (X Y : C.Obj) : Prop :=
  Nonempty (Iso C X Y)

/-- Being isomorphic is an equivalence relation. -/
theorem areIsomorphic_equiv {C : Category} : Equivalence (AreIsomorphic C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X; exact ⟨iso_refl C X⟩
  · intro X Y h; rcases h with ⟨i⟩; exact ⟨iso_symm i⟩
  · intro X Y Z hXY hYZ
    rcases hXY with ⟨i⟩
    rcases hYZ with ⟨j⟩
    exact ⟨iso_trans i j⟩

#eval "Morphisms.Iso: whiskerLeft, whiskerRight, whiskerIso, IsoNatSquare, AreIsomorphic"
#eval s!"Are Bool and Bool isomorphic in SetCat? {AreIsomorphic SetCat Bool Bool}"
#eval s!"Bool iso to Bool via iso_refl: True"
end MiniCategoryCore
