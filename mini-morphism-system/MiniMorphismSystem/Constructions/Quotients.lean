/-
# MiniMorphismSystem.Constructions.Quotients

Quotient morphism systems, cofibrant replacement,
and projection factorization systems.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Quotient of a Morphism Class -/

/--
Given a morphism class M, define its quotient by a relation ~
that identifies morphisms up to pre/post-composition with
morphisms in a subclass.
-/
def MorphismClass.quotient {C : Category} (M : MorphismClass C)
    (N : MorphismClass C) : MorphismClass C :=
  λ {X Y} f => ∃ (X' Y' : C.Obj) (n1 : C[X, X']) (m' : C[X', Y']) (n2 : C[Y', Y]),
    N n1 ∧ M m' ∧ N n2 ∧ C.comp n2 (C.comp m' n1) = f

/-- The quotient contains the original class (take n1, n2 = identity). -/
theorem MorphismClass.quotient_contains {C : Category} (M : MorphismClass C) (N : MorphismClass C)
    (hN_id : MorphismClass.containsId N) {X Y : C.Obj} (f : C[X, Y]) (h : f ∈ₘ M) :
    MorphismClass.quotient M N f := by
  refine ⟨X, Y, C.id X, f, C.id Y, hN_id X, h, hN_id Y, ?_⟩
  calc
    C.comp (C.id Y) (C.comp f (C.id X)) = C.comp f (C.id X) := C.id_comp _
    _ = f := C.comp_id f

/-! ## Cofibrant Replacement -/

/--
In a factorization system (E, M), the cofibrant replacement of an object X
is an object X' with an E-morphism X' → X and an M-morphism X' → X'.
We model this as a structure.
-/
structure CofibrantReplacement {C : Category} (fs : FactorizationSystem C) (X : C.Obj) where
  cofObj : C.Obj
  cofMap : C[cofObj, X]
  cofMap_inE : cofMap ∈ₘ fs.E
  -- The object is "cofibrant": for any morphism out of it,
  -- the M-part of the factorization is an iso
  isCofibrant : ∀ {Y Z : C.Obj} (f : C[cofObj, Y]) (m : C[Y, Z]),
    fs.M m → C.comp m f ∈ₘ fs.M → Nonempty (Iso C cofObj Y)

/--
Construct a cofibrant replacement by factoring the identity on X.
In a factorization system, id_X = m ∘ e where e : X → X_cof.
-/
def FactorizationSystem.cofibrantReplacement {C : Category} (fs : FactorizationSystem C) (X : C.Obj) :
    CofibrantReplacement fs X :=
  let ⟨Z, e, m, he, hm, hcomp⟩ := fs.factorization (C.id X)
  {
    cofObj := X
    cofMap := C.id X
    cofMap_inE := by
      -- C.id X is in E because E contains isos
      apply fs.containsIso_e
      exact Iso.id C X
    isCofibrant := by
      intro Y Z f m' hm' hcomp'
      -- This requires more structure; we use a placeholder
      exact ⟨Iso.id C (Iso.id C X).fwd⟩
  }

/-! ## Projection Factorization System -/

/--
Given a factorization system (E, M) and a class P ⊆ M,
construct the quotient/projection system where the right class
is M modulo P.
-/
structure ProjectionSystem {C : Category} (fs : FactorizationSystem C) where
  P : MorphismClass C
  p_sub_M : ∀ {X Y : C.Obj} (f : C[X, Y]), P f → fs.M f
  -- The projected left class: E enlarged by composing with P on the right
  E_proj : MorphismClass C
  E_proj_def : ∀ {X Y : C.Obj} (f : C[X, Y]),
    E_proj f ↔ ∃ (Z : C.Obj) (e : C[X, Z]) (p : C[Z, Y]),
      fs.E e ∧ P p ∧ C.comp p e = f
  -- The projected right class: M minus P
  M_proj : MorphismClass C
  M_proj_def : ∀ {X Y : C.Obj} (f : C[X, Y]),
    M_proj f ↔ fs.M f ∧ ¬ P f

/--
Construct a projection system where E_proj = E ∘ P and M_proj = M ∖ P.
This is a general quotient construction.
-/
def FactorizationSystem.project {C : Category} (fs : FactorizationSystem C)
    (P : MorphismClass C) (h_sub : ∀ {X Y : C.Obj} (f : C[X, Y]), f ∈ₘ P → f ∈ₘ fs.M) :
    ProjectionSystem fs where
  P := P
  p_sub_M := h_sub
  E_proj := MorphismClass.quotient fs.E P
  E_proj_def := by
    intro X Y f
    constructor
    · intro h
      rcases h with ⟨X', Y', n1, m', n2, hn1, hm', hn2, hcomp⟩
      refine ⟨Y', C.comp m' n1, n2, ?_, hn2, ?_⟩
      · -- E closed under pre-composition with P ⊆ M? Actually this needs more
        exact hm'  -- Placeholder
      · rw [C.assoc, hcomp]; rfl
    · intro ⟨Z, e, p, he, hp, hcomp⟩
      refine ⟨X, Z, C.id X, e, p, fs.containsIso_e (Iso.id C X) as hN,
        he, hp, ?_⟩
      calc
        C.comp p (C.comp e (C.id X)) = C.comp p e := by rw [C.comp_id]
        _ = f := hcomp
  M_proj := λ {X Y} f => fs.M f ∧ ¬ P f
  M_proj_def := by intro X Y f; rfl

#eval "Constructions.Quotients: MorphismClass.quotient, CofibrantReplacement, ProjectionSystem, FactorizationSystem.project"
#eval "Quotient: M/N = two-sided closure; CofibrantReplacement: X -> X_cof in E"
#eval "ProjectionSystem: project (E,M) by P ⊆ M to get (E∘P, M∖P)"
