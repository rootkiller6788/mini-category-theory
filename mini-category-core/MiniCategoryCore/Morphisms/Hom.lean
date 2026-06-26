/-
# MiniCategoryCore.Morphisms.Hom

Special classes of morphisms: monomorphisms, epimorphisms,
split monomorphisms, split epimorphisms, and their relationships.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Monomorphisms -/

/-- A morphism `f` is monic if left-cancellable: `f ∘ g = f ∘ h` implies `g = h`. -/
def Mono {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  ∀ {Z : C.Obj} (g h : C[Z, X]), f ∘ g = f ∘ h → g = h

/-! ## Epimorphisms -/

/-- A morphism `f` is epic if right-cancellable: `g ∘ f = h ∘ f` implies `g = h`. -/
def Epi {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  ∀ {Z : C.Obj} (g h : C[Y, Z]), g ∘ f = h ∘ f → g = h

/-! ## Split Monomorphisms -/

/-- A split monomorphism has a left inverse (retraction). -/
structure SplitMono {C : Category} {X Y : C.Obj} (f : C[X, Y]) where
  retraction : C[Y, X]
  retraction_comp : retraction ∘ f = C.id X

/-- Every split mono is a monomorphism. -/
theorem splitMono_is_mono {C : Category} {X Y : C.Obj} {f : C[X, Y]}
    (sm : SplitMono f) : Mono f := by
  intro Z g h h_eq
  calc
    g = C.id X ∘ g := by rw [C.id_comp]
    _ = (sm.retraction ∘ f) ∘ g := by rw [sm.retraction_comp]
    _ = sm.retraction ∘ (f ∘ g) := by rw [C.assoc]
    _ = sm.retraction ∘ (f ∘ h) := by rw [h_eq]
    _ = (sm.retraction ∘ f) ∘ h := by rw [← C.assoc]
    _ = C.id X ∘ h := by rw [sm.retraction_comp]
    _ = h := by rw [C.id_comp]

/-! ## Split Epimorphisms -/

/-- A split epimorphism has a right inverse (section). -/
structure SplitEpi {C : Category} {X Y : C.Obj} (f : C[X, Y]) where
  section' : C[Y, X]
  comp_section : f ∘ section' = C.id Y

/-- Every split epi is an epimorphism. -/
theorem splitEpi_is_epi {C : Category} {X Y : C.Obj} {f : C[X, Y]}
    (se : SplitEpi f) : Epi f := by
  intro Z g h h_eq
  calc
    g = g ∘ C.id Y := by rw [C.comp_id]
    _ = g ∘ (f ∘ se.section') := by rw [se.comp_section]
    _ = (g ∘ f) ∘ se.section' := by rw [C.assoc]
    _ = (h ∘ f) ∘ se.section' := by rw [h_eq]
    _ = h ∘ (f ∘ se.section') := by rw [← C.assoc]
    _ = h ∘ C.id Y := by rw [se.comp_section]
    _ = h := by rw [C.comp_id]

/-! ## Relationship between Isomorphism and Split Mono/Epi -/

/-- An isomorphism is both a split mono and an epi. -/
theorem iso_is_splitMono_and_epi {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    SplitMono i.hom ∧ Epi i.hom := by
  refine ⟨?_, ?_⟩
  · exact { retraction := i.inv, retraction_comp := i.inv_hom_id }
  · intro Z g h h_eq
    calc
      g = g ∘ C.id Y := by rw [C.comp_id]
      _ = g ∘ (i.hom ∘ i.inv) := by rw [i.hom_inv_id]
      _ = (g ∘ i.hom) ∘ i.inv := by rw [C.assoc]
      _ = (h ∘ i.hom) ∘ i.inv := by rw [h_eq]
      _ = h ∘ (i.hom ∘ i.inv) := by rw [← C.assoc]
      _ = h ∘ C.id Y := by rw [i.hom_inv_id]
      _ = h := by rw [C.comp_id]

/-- Split mono + epi implies isomorphism. -/
theorem splitMono_epi_implies_iso {C : Category} {X Y : C.Obj} {f : C[X, Y]}
    (sm : SplitMono f) (e : Epi f) : IsIso f := by
  have h : (f ∘ sm.retraction) ∘ f = (C.id Y) ∘ f := by
    calc
      (f ∘ sm.retraction) ∘ f = f ∘ (sm.retraction ∘ f) := by rw [← C.assoc]
      _ = f ∘ C.id X := by rw [sm.retraction_comp]
      _ = f := by rw [C.comp_id]
      _ = (C.id Y) ∘ f := by rw [C.id_comp]
  have h_right : f ∘ sm.retraction = C.id Y := e (f ∘ sm.retraction) (C.id Y) h
  exists sm.retraction
  refine ⟨h_right, sm.retraction_comp⟩

/-- A morphism is iso iff it is split mono and epi. -/
theorem isIso_iff_split_mono_epi {C : Category} {X Y : C.Obj} (f : C[X, Y]) :
    IsIso f ↔ SplitMono f ∧ Epi f := by
  constructor
  · intro h
    rcases h with ⟨g, hfg, hgf⟩
    let i : Iso C X Y := { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }
    exact iso_is_splitMono_and_epi i
  · intro ⟨sm, e⟩
    exact splitMono_epi_implies_iso sm e

/-! ## Concrete Examples in SetCat -/

/-- In SetCat, a function is monic iff it is injective. -/
theorem SetCat.mono_iff_injective {X Y : Type u} (f : X → Y) :
    Mono (C := SetCat) f ↔ Function.Injective f := by
  constructor
  · intro hmono a b h
    let ga : Unit → X := λ _ => a
    let gb : Unit → X := λ _ => b
    have h_eq : (f ∘ ga) = (f ∘ gb) := by
      ext u; apply h
    have h' := hmono ga gb h_eq
    have h'' : ga () = gb () := by rw [h']
    simpa [ga, gb] using h''
  · intro hinj Z g h h_eq
    ext z
    apply hinj
    have := congrArg (λ fn : Z → Y => fn z) h_eq
    simpa using this

/-- In SetCat, a function is epic iff it is surjective. -/
theorem SetCat.epi_iff_surjective {X Y : Type u} (f : X → Y) :
    Epi (C := SetCat) f ↔ Function.Surjective f := by
  constructor
  · intro hepi y
    let gy : Y → Prop := λ y' => y' = y
    let hy : Y → Prop := λ _ => True
    have h_eq : (gy ∘ f) = (hy ∘ f) := by
      ext x; simp [gy, hy]
    have h' := hepi gy hy h_eq
    have h_at_y : gy y ↔ hy y := by
      have := congrArg (λ fn : Y → Prop => fn y) h'
      simpa using this
    simp [gy, hy] at h_at_y
    rcases h_at_y with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · intro hsurj Z g h h_eq
    ext y
    rcases hsurj y with ⟨x, hx⟩
    have := congrArg (λ fn : X → Z => fn x) h_eq
    simpa [hx] using this

/-- In SetCat, mono + epi implies iso (split, using classical choice). -/
theorem SetCat.mono_epi_implies_iso {X Y : Type u} (f : X → Y)
    (hm : Mono (C := SetCat) f) (he : Epi (C := SetCat) f) : IsIso (C := SetCat) f := by
  have hinj : Function.Injective f := (SetCat.mono_iff_injective f).mp hm
  have hsurj : Function.Surjective f := (SetCat.epi_iff_surjective f).mp he
  -- Construct a right inverse using choice
  let g : Y → X := λ y => Classical.choose (hsurj y)
  have hgf : ∀ y, f (g y) = y := λ y => Classical.choose_spec (hsurj y)
  have h_right : (f ∘ g) = SetCat.id Y := by
    ext y; apply hgf
  -- Need left inverse: g ∘ f = id X
  -- For each x, we know f (g (f x)) = f x by hgf, so g (f x) = x by injectivity
  have h_left : (g ∘ f) = SetCat.id X := by
    ext x
    apply hinj
    calc
      f (g (f x)) = (f ∘ g) (f x) := rfl
      _ = SetCat.id Y (f x) := by rw [h_right]
      _ = f x := rfl
  exists g
  refine ⟨h_right, h_left⟩

#eval "Morphisms.Hom: Mono, Epi, SplitMono, SplitEpi, iso iff split mono+epi"
#eval s!"id(Bool).retraction_comp: {let sm : SplitMono (SetCat.id Bool) := {retraction := SetCat.id Bool, retraction_comp := SetCat.comp_id (SetCat.id Bool)}; sm.retraction_comp = SetCat.id Bool}"
#eval s!"IsIso(id Bool): {splitMono_epi_implies_iso (let sm : SplitMono (SetCat.id Bool) := {retraction := SetCat.id Bool, retraction_comp := SetCat.comp_id (SetCat.id Bool)}; sm) (by intro Z g h h_eq; exact h_eq)}"
end MiniCategoryCore
