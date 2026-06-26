/-
# MiniCategoryCore.Properties.Invariants

Category invariants: properties that are preserved under equivalence of categories.
Includes: isSkeletal, isGaunt, isGroupoid, isConnected.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Skeletal Categories -/

/-- A category is skeletal if isomorphic objects are equal.
    Equivalently: there is at most one object in each isomorphism class. -/
def isSkeletal (C : Category) : Prop :=
  ∀ (X Y : C.Obj), Nonempty (Iso C X Y) → X = Y

/-- A discrete category is skeletal (all objects are isolated). -/
theorem discrete_is_skeletal (A : Type u) : isSkeletal (DiscCat A) := by
  intro X Y h
  rcases h with ⟨i⟩
  let ULift.up (PLift.up heq) := i.hom
  exact heq

/-! ## Gaunt Categories -/

/-- A category is gaunt if it is skeletal and the only isomorphisms are identities.
    Equivalently: every isomorphism is the identity. -/
def isGaunt (C : Category) : Prop :=
  (∀ (X Y : C.Obj), Nonempty (Iso C X Y) → X = Y) ∧
  (∀ (X : C.Obj) (f : C[X, X]), IsIso f → f = C.id X)

/-- The discrete category is gaunt. -/
theorem discrete_is_gaunt (A : Type u) : isGaunt (DiscCat A) := by
  refine ⟨?_, ?_⟩
  · intro X Y h; rcases h with ⟨i⟩
    let ULift.up (PLift.up heq) := i.hom; exact heq
  · intro X f hf
    rcases hf with ⟨g, hfg, hgf⟩
    -- In DiscCat, all morphisms are ULift(PLift(eq)), and all equalities are by rfl
    -- f is an equality proof, and f ∘ g = id means f.trans(g) = refl
    -- Since f is an iso, f must be refl (up to the PLift/ULift wrapping)
    cases f; cases down; cases down; rfl

/-- The codiscrete category is gaunt iff the type has at most one element. -/
theorem codiscrete_gaunt_iff_subsingleton (A : Type u) :
    isGaunt (CodiscCat A) ↔ (∀ a b : A, a = b) := by
  constructor
  · intro ⟨hskel, _⟩ a b
    let i : Iso (CodiscCat A) a b := {
      hom := OneHom.mk, inv := OneHom.mk,
      hom_inv_id := rfl, inv_hom_id := rfl
    }
    exact hskel a b ⟨i⟩
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro a b _; exact hsub a b
    · intro a f hf
      -- In CodiscCat, there is only OneHom.mk, so f = OneHom.mk = id a
      rfl

/-! ## Groupoid -/

/-- A category is a groupoid if every morphism is an isomorphism. -/
def isGroupoid (C : Category) : Prop :=
  ∀ {X Y : C.Obj} (f : C[X, Y]), IsIso f

/-- The codiscrete category is a groupoid (every morphism has an inverse). -/
theorem codiscrete_is_groupoid (A : Type u) : isGroupoid (CodiscCat A) := by
  intro X Y f
  exists OneHom.mk
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- The discrete category is a groupoid (only identities, which are isos). -/
theorem discrete_is_groupoid (A : Type u) : isGroupoid (DiscCat A) := by
  intro X Y f
  exists (ULift.up (PLift.up (Eq.symm (PLift.down (ULift.down f)))))
  refine ⟨?_, ?_⟩
  · cases f; cases down; cases down; rfl
  · cases f; cases down; cases down; rfl

/-! ## Connected Categories -/

/-- A zigzag is a sequence of forward and backward morphisms connecting two objects. -/
inductive ZigZag {C : Category} : C.Obj → C.Obj → Prop where
  | nil (X : C.Obj) : ZigZag X X
  | cons_fwd {X Y Z : C.Obj} (f : C[X, Y]) : ZigZag Y Z → ZigZag X Z
  | cons_bwd {X Y Z : C.Obj} (f : C[Y, X]) : ZigZag Y Z → ZigZag X Z

/-- A category is connected if any two objects are connected by a zigzag. -/
def isConnected (C : Category) : Prop :=
  ∀ (X Y : C.Obj), ZigZag X Y

/-- The codiscrete category is connected (via a single morphism). -/
theorem codiscrete_is_connected (A : Type u) : isConnected (CodiscCat A) := by
  intro X Y
  apply ZigZag.cons_fwd (f := OneHom.mk)
  apply ZigZag.nil

/-- SetCat is connected: Empty → Unit gives a zigzag between any two types. -/
theorem SetCat_is_connected : isConnected (SetCat : Category) := by
  intro X Y
  -- Use Empty to connect: X ← Empty → Y is a zigzag
  -- But the zigzag only allows forward arrows. Let's use a different path.
  -- fwd: X → Unit (exists), bwd: Unit ← Y means Y → Unit (exists)
  -- So: X → Unit with const(), then from Unit to Y we need Y → Unit going backwards
  -- Actually: cons_fwd (f : X → Unit), then cons_bwd (f : Y → Unit) to get to Y
  -- Wait, cons_bwd takes f : C[Y, X] for ZigZag Y Z → ZigZag X Z
  -- So to go from Unit to Y: need (f : C[Y, Unit]) to go from ZigZag Unit Unit to ZigZag Y Unit.
  -- Hmm, that goes the wrong direction.
  -- Let me trace: cons_fwd f (nil Unit) with f : C[X, Unit] gives ZigZag X Unit
  -- Then cons_bwd g with g : C[Y, Unit] and ZigZag Y Unit (need ZigZag Unit Z for some Z)
  -- The type of cons_bwd: {X Y Z} (f : C[Y, X]) → ZigZag Y Z → ZigZag X Z
  -- We have ZigZag X Unit = ZigZag X Unit, and we want ZigZag X Y
  -- Using cons_bwd (f : C[Y, X]) we go from ZigZag Y Z to ZigZag X Z.
  -- We want to end at Y, so Z = Y and we start from ZigZag Y Z = ZigZag Y Y.
  -- But we have ZigZag X Unit, not ZigZag Y Unit.
  -- Alternative: use Unit as bridge.
  -- ZigZag X Unit (by fwd with f: X→Unit)
  -- ZigZag Unit Y = cons_bwd (g: Y→Unit) from ZigZag Y Y = nil Y?? No, cons_bwd takes Y Z.
  -- Hmm let me think again. cons_bwd {X Y Z : C.Obj} (f : C[Y, X]) : ZigZag Y Z → ZigZag X Z
  -- So: g : C[Y, Unit], need ZigZag Y Unit, get ZigZag Unit Unit
  -- That's zigzag going FROM Unit backwards TO Y.
  -- Wait: cons_bwd f : ZigZag Y Z → ZigZag X Z where f : C[Y, X]
  -- So: X is Unit, Y is Y, f : C[Y, Unit]. This means from ZigZag Y Z we get ZigZag Unit Z.
  -- We want to get ZigZag X Y where X is arbitrary.
  -- Let's do: fwd X→Unit (nil Unit) = ZigZag X Unit
  -- Then: we need to transform ZigZag X Unit into ZigZag X Y
  -- cons_fwd f : ZigZag Y Z → ZigZag X Z with f : C[X, Y]
  -- So to get from ZigZag X Unit to ZigZag X Y, we'd need to change the second index.
  -- Zigzag cons_fwd changes the START, cons_bwd also changes the START!
  -- Hmm, ZigZag connects X to Z, and cons iterates on X.
  -- So ZigZag X Y means: starting at X, following morphisms fwd/bwd, reach Y.
  -- Let me just use a direct approach with the zigzag from X to Empty to Y.
  -- fwd (emptyFn: X→Empty)?? No, X→Empty only exists if X is empty.
  -- OK this is getting too complicated. Let me just say it's connected via Unit.
  -- X → Unit (fwd), then go backwards from Unit to Y: we need f : C[Y, Unit] → ZigZag Y Z → ZigZag Unit Z
  -- If Z = Y: ZigZag Y Y (nil Y) with f: C[Y, Unit] gives ZigZag Unit Y
  -- So: cons_fwd (λ _ => ()) (cons_bwd (λ _ => ()) (nil Y)) : ZigZag X Y
  apply ZigZag.cons_fwd (λ _ : X => ())
  apply ZigZag.cons_bwd (λ _ : Y => ())
  apply ZigZag.nil

#eval "Properties.Invariants: isSkeletal, isGaunt, isGroupoid, isConnected, ZigZag"
#eval s!"DiscCat Nat is skeletal: {discrete_is_skeletal Nat}"
#eval s!"Codiscrete Bool is a groupoid: {codiscrete_is_groupoid Bool}"
#eval s!"SetCat is connected: {SetCat_is_connected}"
end MiniCategoryCore
