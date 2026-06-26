/-
# MiniCategoryCore.Examples.Counterexamples

Counterexamples in category theory: mono + epi that is not iso,
split mono that is not iso, and other illuminating non-examples.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Constructions.Universal

namespace MiniCategoryCore

/-! ## Mono + Epi that is NOT Iso (in a poset category) -/

/-- In the poset category of natural numbers with ≤, every morphism is
    both monic and epic, but the only isos are the identities (reflexive arrows).
    The morphism 0 → 1 is mono + epi but not iso. -/
def twoObjectPoset : Category :=
  PreorderCat (Fin 2) (λ a b => a.val ≤ b.val)
    (λ a => Nat.le_refl _)
    (λ h1 h2 => Nat.le_trans h1 h2)

/-- In a preorder category, every morphism is monic. -/
theorem preorder_cat_all_mono {A : Type u} {R : A → A → Prop} [DecidableRel R]
    (refl : ∀ a, R a a) (trans : ∀ {a b c}, R a b → R b c → R a c)
    {X Y : A} (f : (PreorderCat A R refl trans)[X, Y]) :
    Mono (C := PreorderCat A R refl trans) f := by
  intro Z g h h_eq
  -- In a thin category, all parallel morphisms are equal
  cases g; cases h; rfl

/-- In a preorder category, every morphism is epic. -/
theorem preorder_cat_all_epi {A : Type u} {R : A → A → Prop} [DecidableRel R]
    (refl : ∀ a, R a a) (trans : ∀ {a b c}, R a b → R b c → R a c)
    {X Y : A} (f : (PreorderCat A R refl trans)[X, Y]) :
    Epi (C := PreorderCat A R refl trans) f := by
  intro Z g h h_eq
  cases g; cases h; rfl

/-- In a general preorder, morphisms are mono+epi but not necessarily iso.
    The concrete counterexample uses the 2-element poset below.
    General preorders may lack antisymmetry needed for the proof;
    we demonstrate with the concrete case. -/

/-! ## Concrete Counterexample: 0 ≤ 1 in the two-element poset -/

/-- Build the two-element poset {0 < 1}. -/
def PosetTwo : Category where
  Obj := Fin 2
  Hom X Y := ULift (PLift (X.val ≤ Y.val))
  id X := ULift.up (PLift.up (Nat.le_refl X.val))
  comp g f := ULift.up (PLift.up
    (Nat.le_trans (PLift.down (ULift.down f)) (PLift.down (ULift.down g))))
  comp_id f := by
    cases f; cases down; cases down; rfl
  id_comp f := by
    cases f; cases down; cases down; rfl
  assoc f g h := by
    cases f; cases down; cases down
    cases g; cases down; cases down
    cases h; cases down; cases down; rfl

/-- The morphism 0 → 1 in PosetTwo is mono (since only identity from 0 → 0 can precompose). -/
theorem poset_two_zero_to_one_mono :
    Mono (C := PosetTwo) (ULift.up (PLift.up (by decide : (0 : Fin 2).val ≤ 1.val))) := by
  intro Z g h h_eq
  cases g; cases down; cases down
  cases h; cases down; cases down
  -- Now g and h are both ULift(PLift(≤)) proofs from Z.val to 0.
  -- But the only morphisms to 0 are from 0 itself (since Z.val ≥ 0 always... hmm)
  -- Actually in Fin 2, 0.val ≤ 0 is true, 1.val ≤ 0 is false.
  -- Since both g and h exist (are ULift(PLift(...))), they must both be from 0 to 0.
  -- So g and h are both refl proofs (the only one), hence equal.
  rfl

/-- The morphism 0 → 1 in PosetTwo is epi (since only identity from 1 → 1 can postcompose). -/
theorem poset_two_zero_to_one_epi :
    Epi (C := PosetTwo) (ULift.up (PLift.up (by decide : (0 : Fin 2).val ≤ 1.val))) := by
  intro Z g h h_eq
  cases g; cases down; cases down
  cases h; cases down; cases down
  rfl

/-- But 0 → 1 is NOT iso because there is no morphism 1 → 0. -/
theorem poset_two_zero_to_one_not_iso :
    ¬ IsIso (C := PosetTwo) (ULift.up (PLift.up (by decide : (0 : Fin 2).val ≤ 1.val))) := by
  intro h
  rcases h with ⟨g, hfg, hgf⟩
  -- g : ULift (PLift (1.val ≤ 0.val))
  -- But 1 ≤ 0 is false (since 1 > 0 in Fin 2)
  cases g; cases down; cases down
  -- g is of the form ULift.up (PLift.up h) where h : 1.val ≤ 0.val
  -- But we can derive a contradiction because 1.val = 1, 0.val = 0, and 1 ≤ 0 is false
  have : (1 : Fin 2).val = 1 := rfl
  have : (0 : Fin 2).val = 0 := rfl
  -- Use `by decide` to check the inequality
  decide

/-! ## Non-Split Monomorphism -/

/-- In SetCat, consider the injective function f : Empty → Unit.
    f is monic (injective) but has no retraction because there is no map Unit → Empty. -/
theorem empty_to_unit_mono : Mono (C := SetCat) (λ (_ : Empty) => ()) := by
  intro Z g h h_eq
  ext z
  -- g z and h z must be equal for all z:Z... but wait, this only works if Z → Empty
  -- The function g: Z → Empty can only exist if Z is also empty (or we're using Empty.rec)
  -- Since h_eq : (λ _ => ()) ∘ g = (λ _ => ()) ∘ h
  -- Both sides are functions Z → Unit, so they're equal trivially
  -- But from this we need g = h, which is true because there's at most one function to Empty
  -- Actually, g z : Empty, and we can use Empty.rec on it
  exact (g z).elim

/-- The function Empty → Unit is monic but NOT split mono (no retraction exists). -/
theorem empty_to_unit_not_split_mono :
    ¬ SplitMono (C := SetCat) (λ (_ : Empty) => ()) := by
  intro h
  have retr := h.retraction ()
  -- retr : Empty, which is impossible
  exact retr.elim

#eval "Examples.Counterexamples: Mono+Epi not Iso (poset), non-split mono (Empty→Unit)"
#eval "In PosetTwo, 0→1 is mono and epi but not iso"
#eval "In SetCat, Empty→Unit is mono but not split mono"
end MiniCategoryCore
