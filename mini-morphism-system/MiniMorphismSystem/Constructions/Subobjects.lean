/-
# MiniMorphismSystem.Constructions.Subobjects

Subobject of morphisms, restriction of factorization systems,
and sub-morphism systems.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Sub-MorphismClass -/

/--
A sub-morphism class: restrict a morphism class to a condition.
-/
def MorphismClass.sub {C : Category} (M : MorphismClass C) (P : C.Obj → Prop) : MorphismClass C :=
  λ {X Y} f => M f ∧ P X ∧ P Y

/-- The full sub-morphism class on a subclass of objects. -/
def MorphismClass.fullOn {C : Category} (P : C.Obj → Prop) : MorphismClass C :=
  λ {X Y} _ => P X ∧ P Y

/-- Restrict a morphism class to those morphisms between objects satisfying P. -/
def MorphismClass.restrict {C : Category} (M : MorphismClass C) (P : C.Obj → Prop) : MorphismClass C :=
  λ {X Y} f => M f ∧ P X ∧ P Y

/-! ## Restriction of Factorization System -/

/--
Given a factorization system on C and a predicate P on objects,
restrict the factorization system to the full subcategory on P.
-/
structure RestrictedFactorizationSystem {C : Category}
    (fs : FactorizationSystem C) (P : C.Obj → Prop) where
  E_restricted : MorphismClass C
  M_restricted : MorphismClass C
  e_sub : ∀ {X Y : C.Obj} (f : C[X, Y]), E_restricted f → fs.E f ∧ P X ∧ P Y
  m_sub : ∀ {X Y : C.Obj} (f : C[X, Y]), M_restricted f → fs.M f ∧ P X ∧ P Y
  factorization_restricted : ∀ {X Y : C.Obj} (f : C[X, Y]),
    P X → P Y → ∃ (Z : C.Obj) (e : C[X, Z]) (m : C[Z, Y]),
      E_restricted e ∧ M_restricted m ∧ C.comp m e = f
  orthogonal_restricted : ∀ {A B X Y : C.Obj} {e : C[A, B]} {m : C[X, Y]},
    E_restricted e → M_restricted m → e ⋔ m

/--
Construct a restricted factorization system from a full one
by taking E and M to be the restrictions.
-/
def FactorizationSystem.restrict {C : Category} (fs : FactorizationSystem C) (P : C.Obj → Prop)
    (h_closed : ∀ {X Y : C.Obj} (f : C[X, Y]), P X → fs.E f → P Y)
    (h_closedM : ∀ {X Y : C.Obj} (f : C[X, Y]), P X → fs.M f → P Y) :
    RestrictedFactorizationSystem fs P where
  E_restricted := MorphismClass.restrict fs.E P
  M_restricted := MorphismClass.restrict fs.M P
  e_sub := by
    intro X Y f h
    rcases h with ⟨hE, hPX, hPY⟩
    exact ⟨hE, hPX, hPY⟩
  m_sub := by
    intro X Y f h
    rcases h with ⟨hM, hPX, hPY⟩
    exact ⟨hM, hPX, hPY⟩
  factorization_restricted := by
    intro X Y f hPX hPY
    rcases fs.factorization f with ⟨Z, e, m, he, hm, hcomp⟩
    have hPZ : P Z := h_closed e hPX he
    refine ⟨Z, e, m, ⟨he, hPX, hPZ⟩, ⟨hm, hPZ, hPY⟩, hcomp⟩
  orthogonal_restricted := by
    intro A B X Y e m he hm u v hsq
    rcases he with ⟨heE, _, _⟩
    rcases hm with ⟨hmM, _, _⟩
    exact fs.orthogonal e m heE hmM u v hsq

/-! ## Subobject of a Morphism -/

/--
A subobject of a morphism f : X → Y is a factorization
f = m ∘ e through an intermediate object where m is monic.
We model this as an object Z with morphisms e,m.
-/
structure SubobjectOfMorphism {C : Category} {X Y : C.Obj} (f : C[X, Y]) where
  Z : C.Obj
  e : C[X, Z]
  m : C[Z, Y]
  decomp : C.comp m e = f
  m_mono : ∀ {W : C.Obj} (g₁ g₂ : C[W, Z]), C.comp m g₁ = C.comp m g₂ → g₁ = g₂

/--
An image of a morphism f is a subobject through which f factors
such that e is epic.
-/
structure ImageFactorization {C : Category} {X Y : C.Obj} (f : C[X, Y]) extends SubobjectOfMorphism f where
  e_epi : ∀ {W : C.Obj} (g₁ g₂ : C[Z, W]), C.comp g₁ e = C.comp g₂ e → g₁ = g₂

/-! ## Sub-Morphism System -/

/--
A sub-system of a factorization system: (E', M') where E' ⊆ E, M' ⊆ M,
and the factorization of E'-M' is given by the larger one.
-/
structure SubFactorizationSystem {C : Category} (fs : FactorizationSystem C) where
  E' : MorphismClass C
  M' : MorphismClass C
  e_sub : ∀ {X Y : C.Obj} (f : C[X, Y]), E' f → fs.E f
  m_sub : ∀ {X Y : C.Obj} (f : C[X, Y]), M' f → fs.M f
  containsIso_e' : ∀ {X Y : C.Obj} (i : Iso C X Y), i.fwd ∈ₘ E'
  containsIso_m' : ∀ {X Y : C.Obj} (i : Iso C X Y), i.fwd ∈ₘ M'

/--
Every factorization system is trivially a sub-system of itself.
-/
def FactorizationSystem.asSubSelf {C : Category} (fs : FactorizationSystem C) :
    SubFactorizationSystem fs where
  E' := fs.E
  M' := fs.M
  e_sub _ _ h := h
  m_sub _ _ h := h
  containsIso_e' i := fs.containsIso_e i
  containsIso_m' i := fs.containsIso_m i

#eval "Constructions.Subobjects: MorphismClass.sub/fullOn/restrict, RestrictedFactorizationSystem, SubobjectOfMorphism, ImageFactorization, SubFactorizationSystem"
#eval "Restricted FS: restrict (E,M) to objects satisfying a predicate"
#eval "Subobject of morphism: f = m ∘ e with m monic; Image adds e epic"
