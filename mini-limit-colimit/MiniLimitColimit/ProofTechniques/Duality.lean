/-
# MiniLimitColimit.ProofTechniques.Duality

## Knowledge Coverage
- L5: Proof by duality - colimit theorems from limit theorems
- L4: Dualization of universal properties
- L6: Concrete examples of dual constructions in SetCat
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Constructions.Universal
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients
import MiniLimitColimit.Morphisms.Hom
import MiniLimitColimit.Morphisms.Equivalence

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Duality Principle (L5: Proof Technique)

The duality principle in category theory states that for any theorem
about categories, reversing all arrows (passing to the opposite category)
yields another valid theorem. For limits and colimits specifically:

  "A colimit of D in C is a limit of D in C.op" (and vice versa).

This file demonstrates the duality technique through:
1. Direct dual constructions (product-coproduct, equalizer-coequalizer, etc.)
2. Proof transfer: deriving colimit theorems from limit theorems
3. Self-dual concepts vs non-self-dual concepts
-/

/-! ### Dual Construction: Product to Coproduct (via op) -/

theorem product_is_coproduct_in_op {C : Category} {A B P : C.Obj}
    (prod : IsProduct A B P) : IsCoproduct (C := Category.op C) A B P := by
  refine {
    inl := prod.fst
    inr := prod.snd
    mediate f g := prod.mediate g f
    inl_mediate f g := prod.fst_mediate g f
    inr_mediate f g := prod.snd_mediate g f
    unique f g h h1 h2 := prod.unique g f h h2 h1
  }

theorem coproduct_is_product_in_op {C : Category} {A B CP : C.Obj}
    (coprod : IsCoproduct A B CP) : IsProduct (C := Category.op C) A B CP := by
  refine {
    fst := coprod.inl
    snd := coprod.inr
    mediate f g := coprod.mediate g f
    fst_mediate f g := coprod.inl_mediate g f
    snd_mediate f g := coprod.inr_mediate g f
    unique f g h h1 h2 := coprod.unique g f h h2 h1
  }

/-! ### Dual Construction: Equalizer to Coequalizer -/

theorem equalizer_is_coequalizer_in_op {C : Category} {A B : C.Obj} {f g : C[A, B]}
    (eq : Equalizer f g) : Coequalizer (C := Category.op C) f g := by
  refine {
    cofork := {
      obj := eq.fork.obj
      coforkMap := eq.fork.forkMap
      condition := eq.fork.condition
    }
    mediate c := eq.mediate {
      obj := c.obj
      forkMap := c.coforkMap
      condition := c.condition
    }
    factor c := eq.factor {
      obj := c.obj
      forkMap := c.coforkMap
      condition := c.condition
    }
    unique c h h_eq := eq.unique {
      obj := c.obj
      forkMap := c.coforkMap
      condition := c.condition
    } h h_eq
  }

theorem coequalizer_is_equalizer_in_op {C : Category} {A B : C.Obj} {f g : C[A, B]}
    (coeq : Coequalizer f g) : Equalizer (C := Category.op C) f g := by
  refine {
    fork := {
      obj := coeq.cofork.obj
      forkMap := coeq.cofork.coforkMap
      condition := coeq.cofork.condition
    }
    mediate f' := coeq.mediate {
      obj := f'.obj
      coforkMap := f'.forkMap
      condition := f'.condition
    }
    factor f' := coeq.factor {
      obj := f'.obj
      coforkMap := f'.forkMap
      condition := f'.condition
    }
    unique f' h h_eq := coeq.unique {
      obj := f'.obj
      coforkMap := f'.forkMap
      condition := f'.condition
    } h h_eq
  }

/-! ### Dual Construction: Pullback to Pushout -/

theorem pullback_is_pushout_in_op {C : Category} {A B D : C.Obj}
    {f : C[A, D]} {g : C[B, D]} (pb : Pullback f g) : Pushout (C := Category.op C) f g := by
  refine {
    cocone := {
      nadir := pb.cone.apex
      u := pb.cone.p
      v := pb.cone.q
      commutes := pb.cone.commutes
    }
    mediate c := pb.mediate {
      apex := c.nadir
      p := c.u
      q := c.v
      commutes := c.commutes
    }
    factor_u c := pb.factor_p {
      apex := c.nadir
      p := c.u
      q := c.v
      commutes := c.commutes
    }
    factor_v c := pb.factor_q {
      apex := c.nadir
      p := c.u
      q := c.v
      commutes := c.commutes
    }
    unique c h h1 h2 := pb.unique {
      apex := c.nadir
      p := c.u
      q := c.v
      commutes := c.commutes
    } h h1 h2
  }

theorem pushout_is_pullback_in_op {C : Category} {A B X : C.Obj}
    {f : C[X, A]} {g : C[X, B]} (po : Pushout f g) : Pullback (C := Category.op C) f g := by
  refine {
    cone := {
      apex := po.cocone.nadir
      p := po.cocone.u
      q := po.cocone.v
      commutes := po.cocone.commutes
    }
    mediate c := po.mediate {
      nadir := c.apex
      u := c.p
      v := c.q
      commutes := c.commutes
    }
    factor_p c := po.factor_u {
      nadir := c.apex
      u := c.p
      v := c.q
      commutes := c.commutes
    }
    factor_q c := po.factor_v {
      nadir := c.apex
      u := c.p
      v := c.q
      commutes := c.commutes
    }
    unique c h h1 h2 := po.unique {
      nadir := c.apex
      u := c.p
      v := c.q
      commutes := c.commutes
    } h h1 h2
  }

/-! ### Proof Transfer: Deriving Colimit Uniqueness via Duality -/

theorem colimit_uniqueness_by_duality {J C : Category} {D : Diagram J C} (C1 C2 : Colimit D) :
    IsIso (colimitUniqueInv C1 C2) :=
  colimitIsIsoUnique C1 C2

def proofTransfer_example : String :=
  "Pattern: limit theorem T -> apply op -> colimit theorem T*"

/-! ### Self-Dual Concepts -/

theorem iso_is_self_dual {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    Iso (Category.op C) X Y where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.inv_hom_id
  inv_hom_id := i.hom_inv_id

theorem initial_is_terminal_in_op {C : Category} (I : Initial C) :
    Terminal (Category.op C) where
  obj := I.obj
  terminate X := I.initiate X
  unique X f := I.unique X f

theorem terminal_is_initial_in_op {C : Category} (T : Terminal C) :
    Initial (Category.op C) where
  obj := T.obj
  initiate X := T.terminate X
  unique X f := T.unique X f

/-! ### Limit-Cone Duality in ConeCat -/

theorem limit_is_terminal_cone {J C : Category} {D : Diagram J C} (L : Limit D) :
    Terminal (ConeCat D) where
  obj := L.limitCone
  terminate c := Subtype.mk (L.mediate c) (fun j => L.factor c j)
  unique c f := by
    rcases f with ⟨f', hf⟩
    apply Subtype.ext
    apply L.unique c f' hf

theorem colimit_is_initial_cocone {J C : Category} {D : Diagram J C} (CL : Colimit D) :
    Initial (CoconeCat D) where
  obj := CL.colimitCocone
  initiate c := Subtype.mk (CL.mediate c) (fun j => CL.factor c j)
  unique c f := by
    rcases f with ⟨f', hf⟩
    apply Subtype.ext
    apply CL.unique c f' hf

/-! ### Concrete Duality Examples in SetCat -/

def duality_product_example : IsProduct SetCat Nat Bool (Prod Nat Bool) := productOfPairInSet
def duality_coproduct_example : IsCoproduct SetCat Nat Bool (Sum Nat Bool) := coproductOfPairInSet

def duality_mediate_demo (Q : Type) (f : Q → Nat) (g : Q → Bool) : Q → Prod Nat Bool :=
  duality_product_example.mediate f g

def duality_comediate_demo (Q : Type) (f : Nat → Q) (g : Bool → Q) : Sum Nat Bool → Q :=
  duality_coproduct_example.mediate f g

/-! ## #eval Examples -/

#eval "ProofTechniques.Duality: product-coproduct, equalizer-coequalizer, pullback-pushout"
#eval (duality_product_example : IsProduct _ _ _ _).fst (3, true)
#eval (duality_coproduct_example : IsCoproduct _ _ _ _).inl 42
#eval (iso_is_self_dual (limitIso exLimit exLimit)).hom ()
#eval proofTransfer_example

end MiniLimitColimit
