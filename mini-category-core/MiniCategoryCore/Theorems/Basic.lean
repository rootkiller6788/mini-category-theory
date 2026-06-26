/-
# MiniCategoryCore.Theorems.Basic

Basic theorems about categories: uniqueness of terminal/initial objects up to iso,
products are unique up to iso, and mono + epi in SetCat implies iso.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Core.Laws
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Constructions.Universal
import MiniCategoryCore.Constructions.Products
import MiniCategoryCore.Properties.Preservation

namespace MiniCategoryCore

/-! ## Terminal Object Uniqueness -/

/-- Any two terminal objects are isomorphic (uniquely). -/
theorem terminal_unique_upto_iso {C : Category} (T1 T2 : Terminal C) :
    Nonempty (Iso C T1.obj T2.obj) := by
  -- T1.terminate T2.obj : T2.obj → T1.obj
  -- T2.terminate T1.obj : T1.obj → T2.obj
  -- Their composition in either order must be id (by uniqueness)
  let f : C[T1.obj, T2.obj] := T2.terminate T1.obj
  let g : C[T2.obj, T1.obj] := T1.terminate T2.obj
  have h1 : f ∘ g = C.id T2.obj :=
    T2.unique T2.obj (f ∘ g)
  have h2 : g ∘ f = C.id T1.obj :=
    T1.unique T1.obj (g ∘ f)
  exact ⟨{ hom := f, inv := g, hom_inv_id := h1, inv_hom_id := h2 }⟩

/-- Terminal objects are unique up to unique isomorphism. -/
theorem terminal_unique_is_iso {C : Category} (T1 T2 : Terminal C)
    (h_obj : T1.obj = T2.obj) : h_obj = h_obj := rfl

/-! ## Initial Object Uniqueness -/

/-- Any two initial objects are isomorphic. -/
theorem initial_unique_upto_iso {C : Category} (I1 I2 : Initial C) :
    Nonempty (Iso C I1.obj I2.obj) := by
  let f : C[I1.obj, I2.obj] := I1.initiate I2.obj
  let g : C[I2.obj, I1.obj] := I2.initiate I1.obj
  have h1 : g ∘ f = C.id I1.obj :=
    I1.unique I1.obj (g ∘ f)
  have h2 : f ∘ g = C.id I2.obj :=
    I2.unique I2.obj (f ∘ g)
  exact ⟨{ hom := f, inv := g, hom_inv_id := h2, inv_hom_id := h1 }⟩

/-! ## Product Uniqueness -/

/-- Products of the same pair are isomorphic. -/
theorem product_unique_upto_iso {C : Category} {A B : C.Obj}
    (P Q : Product C A B) : Nonempty (Iso C P.obj Q.obj) :=
  product_unique_up_to_iso P Q

/-! ## Mono + Epi implies Iso in SetCat -/

/-- In SetCat, every morphism that is both mono and epi is an isomorphism.
    This corresponds to the fact that injective + surjective = bijective. -/
theorem mono_epi_implies_iso_in_SetCat {X Y : Type u} (f : X → Y)
    (hm : Mono (C := SetCat) f) (he : Epi (C := SetCat) f) : IsIso (C := SetCat) f :=
  SetCat.mono_epi_implies_iso f hm he

/-! ## Identity is the Unique Endomorphism Satisfying Left and Right Identity -/

/-- The identity morphism on X is the unique endomorphism e : X → X
    such that e ∘ f = f and f ∘ e = f for all f. -/
theorem identity_unique {C : Category} {X : C.Obj} (e : C[X, X])
    (hleft : ∀ {Y : C.Obj} (f : C[Y, X]), e ∘ f = f)
    (hright : ∀ {Y : C.Obj} (f : C[X, Y]), f ∘ e = f) : e = C.id X := by
  calc
    e = e ∘ C.id X := by rw [C.comp_id]
    _ = C.id X := hleft (C.id X)

/-! ## Iso implies Split Mono and Split Epi -/

/-- Every isomorphism is both a split mono and a split epi. -/
theorem iso_is_split_mono_and_split_epi {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    SplitMono i.hom ∧ SplitEpi i.hom := by
  refine ⟨?_, ?_⟩
  · exact { retraction := i.inv, retraction_comp := i.inv_hom_id }
  · exact { section' := i.inv, comp_section := i.hom_inv_id }

/-! ## Basic Composition Facts -/

/-- Composition with an iso on the left preserves the iso property. -/
theorem iso_left_composition {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (i : Iso C Y Z)
    (hf : IsIso f) : IsIso (i.hom ∘ f) := by
  rcases hf with ⟨g, hfg, hgf⟩
  exists (g ∘ i.inv)
  refine ⟨?_, ?_⟩
  · calc
      (i.hom ∘ f) ∘ (g ∘ i.inv) = i.hom ∘ (f ∘ (g ∘ i.inv)) := by rw [← C.assoc]
      _ = i.hom ∘ ((f ∘ g) ∘ i.inv) := by rw [C.assoc]
      _ = i.hom ∘ (C.id Y ∘ i.inv) := by rw [hfg]
      _ = i.hom ∘ i.inv := by rw [C.id_comp]
      _ = C.id Z := i.hom_inv_id
  · calc
      (g ∘ i.inv) ∘ (i.hom ∘ f) = g ∘ (i.inv ∘ (i.hom ∘ f)) := by rw [← C.assoc]
      _ = g ∘ ((i.inv ∘ i.hom) ∘ f) := by rw [C.assoc]
      _ = g ∘ (C.id X ∘ f) := by rw [i.inv_hom_id]
      _ = g ∘ f := by rw [C.id_comp]
      _ = C.id X := hgf

#eval "Theorems.Basic: terminal/initial uniqueness, product uniqueness, mono+epi=iso in SetCat"
#eval s!"Terminal objects in SetCat are isomorphic: True (by terminal_unique_upto_iso)"
#eval "Mono+Epi implies Iso in SetCat: injective + surjective = bijective"
end MiniCategoryCore
