/-
# MiniCategoryCore.Properties.Preservation

Properties preserved by isomorphisms and under morphism composition:
terminality, initiality, monicity, epicity.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Constructions.Universal

namespace MiniCategoryCore

/-! ## Terminal Objects are Preserved by Isomorphism -/

/-- If T is terminal and T ≅ T', then T' is also terminal. -/
theorem terminal_preserved_by_iso {C : Category} {T T' : C.Obj}
    (hT : Terminal C) (hT_eq : hT.obj = T) (i : Iso C T T') : Terminal C := by
  subst hT_eq
  have h : ∀ (X : C.Obj), C[X, T] := hT.terminate
  have huniq : ∀ (X : C.Obj) (f : C[X, T]), f = hT.terminate X := hT.unique
  refine {
    obj := T',
    terminate := λ X => i.hom ∘ hT.terminate X,
    unique := λ X f => ?_
  }
  -- Any f : X → T' factors through T
  have h_inv : i.inv ∘ f = h X := huniq X (i.inv ∘ f)
  calc
    f = C.id T' ∘ f := by rw [C.id_comp]
    _ = (i.hom ∘ i.inv) ∘ f := by rw [i.hom_inv_id]
    _ = i.hom ∘ (i.inv ∘ f) := by rw [C.assoc]
    _ = i.hom ∘ h X := by rw [h_inv]
    _ = i.hom ∘ hT.terminate X := rfl

/-- If I is initial and I ≅ I', then I' is also initial. -/
theorem initial_preserved_by_iso {C : Category} {I I' : C.Obj}
    (hI : Initial C) (hI_eq : hI.obj = I) (i : Iso C I I') : Initial C := by
  subst hI_eq
  have h : ∀ (X : C.Obj), C[I, X] := hI.initiate
  have huniq : ∀ (X : C.Obj) (f : C[I, X]), f = hI.initiate X := hI.unique
  refine {
    obj := I',
    initiate := λ X => h X ∘ i.inv,
    unique := λ X f => ?_
  }
  -- Any f : I' → X factors as (initiate X) ∘ i.inv
  have h_hom : f ∘ i.hom = h X := huniq X (f ∘ i.hom)
  calc
    f = f ∘ C.id I' := by rw [C.comp_id]
    _ = f ∘ (i.hom ∘ i.inv) := by rw [i.hom_inv_id]
    _ = (f ∘ i.hom) ∘ i.inv := by rw [C.assoc]
    _ = h X ∘ i.inv := by rw [h_hom]
    _ = hI.initiate X ∘ i.inv := rfl

/-! ## Monicity Preserved by Composition -/

/-- If f and g are monic, then g ∘ f is monic. -/
theorem mono_composition {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z])
    (hm_f : Mono f) (hm_g : Mono g) : Mono (g ∘ f) := by
  intro W h1 h2 h_eq
  have h_eq1 : g ∘ (f ∘ h1) = g ∘ (f ∘ h2) := by
    calc
      g ∘ (f ∘ h1) = (g ∘ f) ∘ h1 := by rw [C.assoc]
      _ = (g ∘ f) ∘ h2 := by rw [h_eq]
      _ = g ∘ (f ∘ h2) := by rw [C.assoc]
  have hm_g_res := hm_g (f ∘ h1) (f ∘ h2) h_eq1
  have hm_f_res := hm_f h1 h2 hm_g_res
  exact hm_f_res

/-- If g ∘ f is monic, then f is monic. -/
theorem mono_cancel_left {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z])
    (hm : Mono (g ∘ f)) : Mono f := by
  intro W h1 h2 h_eq
  apply hm h1 h2
  calc
    (g ∘ f) ∘ h1 = g ∘ (f ∘ h1) := by rw [C.assoc]
    _ = g ∘ (f ∘ h2) := by rw [h_eq]
    _ = (g ∘ f) ∘ h2 := by rw [C.assoc]

/-- If f is a split mono, then g ∘ f is a split mono for any g where composition makes sense. -/
theorem splitMono_composition {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z])
    (sm : SplitMono f) (sm_g : SplitMono g) : SplitMono (g ∘ f) := by
  -- retraction is sm.retraction ∘ sm_g.retraction
  refine {
    retraction := sm.retraction ∘ sm_g.retraction,
    retraction_comp := ?
  }
  calc
    (sm.retraction ∘ sm_g.retraction) ∘ (g ∘ f) = sm.retraction ∘ (sm_g.retraction ∘ (g ∘ f)) := by rw [← C.assoc]
    _ = sm.retraction ∘ ((sm_g.retraction ∘ g) ∘ f) := by rw [C.assoc]
    _ = sm.retraction ∘ (C.id Y ∘ f) := by rw [sm_g.retraction_comp]
    _ = sm.retraction ∘ f := by rw [C.id_comp]
    _ = C.id X := sm.retraction_comp

/-! ## Epicity Preserved by Composition -/

/-- If f and g are epic, then g ∘ f is epic. -/
theorem epi_composition {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z])
    (he_f : Epi f) (he_g : Epi g) : Epi (g ∘ f) := by
  intro W h1 h2 h_eq
  have h_eq1 : h1 ∘ g = h2 ∘ g := by
    apply he_f
    calc
      (h1 ∘ g) ∘ f = h1 ∘ (g ∘ f) := by rw [← C.assoc]
      _ = h2 ∘ (g ∘ f) := by rw [h_eq]
      _ = (h2 ∘ g) ∘ f := by rw [← C.assoc]
  exact he_g h1 h2 h_eq1

/-- If g ∘ f is epic, then g is epic. -/
theorem epi_cancel_right {C : Category} {X Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z])
    (he : Epi (g ∘ f)) : Epi g := by
  intro W h1 h2 h_eq
  apply he h1 h2
  calc
    h1 ∘ (g ∘ f) = (h1 ∘ g) ∘ f := by rw [C.assoc]
    _ = (h2 ∘ g) ∘ f := by rw [h_eq]
    _ = h2 ∘ (g ∘ f) := by rw [C.assoc]

#eval "Properties.Preservation: terminal/initial preserved, mono/epi composition"
#eval s!"Mono composition: Always true for SetCat identity maps"
#eval "Epi composition: Same pattern as mono"
end MiniCategoryCore
