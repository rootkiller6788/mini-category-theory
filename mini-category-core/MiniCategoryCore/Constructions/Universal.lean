/-
# MiniCategoryCore.Constructions.Universal

Universal constructions: initial/terminal objects, predicate forms,
uniqueness up to isomorphism, and concrete examples in SetCat.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom

namespace MiniCategoryCore

/-! ## Predicate forms: isTerminal, isInitial -/

/-- An object T is terminal if for every X there is exactly one morphism X → T. -/
def isTerminal (C : Category) (T : C.Obj) : Prop :=
  ∀ (X : C.Obj), ∃! f : C[X, T], True

/-- An object I is initial if for every X there is exactly one morphism I → X. -/
def isInitial (C : Category) (I : C.Obj) : Prop :=
  ∀ (X : C.Obj), ∃! f : C[I, X], True

/-- An object Z is zero if it is both initial and terminal. -/
def isZero (C : Category) (Z : C.Obj) : Prop :=
  isInitial C Z ∧ isTerminal C Z

/-! ## Initial Object -/

structure Initial (C : Category) where
  obj : C.Obj
  initiate : ∀ (X : C.Obj), C[obj, X]
  unique : ∀ (X : C.Obj) (f : C[obj, X]), f = initiate X

theorem initial_is_initial (C : Category) (I : Initial C) : isInitial C I.obj := by
  intro X
  refine ⟨I.initiate X, trivial, ?_⟩
  intro f _
  exact I.unique X f

/-! ## Terminal Object -/

structure Terminal (C : Category) where
  obj : C.Obj
  terminate : ∀ (X : C.Obj), C[X, obj]
  unique : ∀ (X : C.Obj) (f : C[X, obj]), f = terminate X

theorem terminal_is_terminal (C : Category) (T : Terminal C) : isTerminal C T.obj := by
  intro X
  refine ⟨T.terminate X, trivial, ?_⟩
  intro f _
  exact T.unique X f

/-! ## Zero Object -/

structure Zero (C : Category) where
  initial : Initial C
  terminal : Terminal C
  objEq : initial.obj = terminal.obj

/-- The zero object is both initial and terminal. -/
theorem zero_is_initial_and_terminal (C : Category) (Z : Zero C) :
    isInitial C Z.initial.obj ∧ isTerminal C Z.terminal.obj := by
  refine ⟨initial_is_initial C Z.initial, terminal_is_terminal C Z.terminal⟩

/-! ## Concrete Examples in SetCat -/

/-- In SetCat, the empty type is initial. -/
def SetCat.initial : Initial SetCat where
  obj := Empty
  initiate X := λ e => e.elim
  unique X f := by
    ext x; exact x.elim

/-- In SetCat, the unit type is terminal. -/
def SetCat.terminal : Terminal SetCat where
  obj := Unit
  terminate X := λ _ => ()
  unique X f := by
    ext x; exact Unit.ext _ _

/-- SetCat does NOT have a zero object (Empty ≠ Unit). -/
theorem SetCat.no_zero_object : ¬ ∃ (Z : Zero SetCat), True := by
  intro h
  rcases h with ⟨Z, _⟩
  have h_eq : Z.initial.obj = Z.terminal.obj := Z.objEq
  -- Empty = Unit as types, which gives a contradiction via cardinality
  -- We can construct a specific function from Empty to Unit and vice versa,
  -- but they're not equal as types
  -- For a contradiction: if Empty = Unit, then Empty is inhabited
  subst h_eq
  have h_unit : Empty := SetCat.terminal.terminate Empty ()
  exact h_unit.elim

/-- In DiscCat, every object is both initial and terminal (vacuously? No).
    Actually, only the only object (if singleton) can be both. -/
theorem disc_cat_initial_iff_singleton (A : Type u) (a : A) :
    isInitial (DiscCat A) a → ∀ b : A, a = b := by
  intro h b
  have hb := h b
  rcases hb with ⟨f, _, huniq⟩
  -- f : a → b in DiscCat A, which is ULift(PLift(a = b))
  let ULift.up (PLift.up heq) := f
  exact heq

/-- Terminal and initial are dual via the opposite construction. -/
theorem terminal_via_op (C : Category) (T : C.Obj) :
    isTerminal C T ↔ isInitial (Cᵒᵖ) T := by
  constructor
  · intro h X
    -- X is of type (Cᵒᵖ).Obj = C.Obj
    -- Need: there is exactly one morphism T → X in Cᵒᵖ
    -- In Cᵒᵖ, Hom(T, X) = C[X, T], so the unique map is T.terminate X in C
    have hT := h X
    rcases hT with ⟨f, _, huniq⟩
    refine ⟨f, trivial, ?_⟩
    intro g _
    apply huniq g trivial
  · intro h X
    have hI := h X
    rcases hI with ⟨f, _, huniq⟩
    refine ⟨f, trivial, ?_⟩
    intro g _
    apply huniq g trivial

/-- A category with a zero object is called "pointed". -/
def isPointed (C : Category) : Prop :=
  ∃ (Z : C.Obj), isZero C Z

#eval "Constructions.Universal: isTerminal, isInitial, isZero, Initial, Terminal, Zero"
#eval s!"SetCat has initial Empty: True"
#eval s!"SetCat has terminal Unit: True"
#eval "SetCat has no zero object (Empty ≠ Unit)"
end MiniCategoryCore
