/-
# MiniMorphismSystem.Constructions.Products

Product factorization systems, lifting in product categories,
and morphisms in product categories.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Product of Categories -/

/-- The product of two categories C × D (existing definition from MiniCategoryCore). -/
-- Category.prod is already defined in MiniCategoryCore

/-- A morphism in a product category is a pair of morphisms. -/
def ProdHom.fst {C D : Category} {X Y : (C ×ᶜ D).Obj} (f : (C ×ᶜ D)[X, Y]) : C[X.1, Y.1] :=
  f.1

def ProdHom.snd {C D : Category} {X Y : (C ×ᶜ D).Obj} (f : (C ×ᶜ D)[X, Y]) : D[X.2, Y.2] :=
  f.2

/-- Pair two morphisms into a product category morphism. -/
def ProdHom.mk {C D : Category} {X Y : (C ×ᶜ D).Obj}
    (f : C[X.1, Y.1]) (g : D[X.2, Y.2]) : (C ×ᶜ D)[X, Y] := (f, g)

/-! ## Product of Morphism Classes -/

/-- Given morphism classes on C and D, form a morphism class on C × D. -/
def MorphismClass.prod {C D : Category} (Mc : MorphismClass C) (Md : MorphismClass D) :
    MorphismClass (C ×ᶜ D) :=
  λ {X Y} φ => Mc (ProdHom.fst φ) ∧ Md (ProdHom.snd φ)

notation Mc:40 " ×ₘ " Md:40 => MorphismClass.prod Mc Md

/-- The product morphism class contains isomorphisms if the components do. -/
theorem MorphismClass.prod_containsIso {C D : Category}
    (Mc : MorphismClass C) (Md : MorphismClass D)
    (hMc : ∀ {X Y : C.Obj} (i : Iso C X Y), i.fwd ∈ₘ Mc)
    (hMd : ∀ {X Y : D.Obj} (i : Iso D X Y), i.fwd ∈ₘ Md)
    {X Y : (C ×ᶜ D).Obj} (i : Iso (C ×ᶜ D) X Y) : i.fwd ∈ₘ (Mc ×ₘ Md) := by
  -- An iso in C × D has iso components
  refine ⟨?_, ?_⟩
  · apply hMc
    refine {
      fwd := ProdHom.fst i.fwd
      rev := ProdHom.fst i.rev
      fwd_rev := ?_
      rev_fwd := ?_
    }
    · have := i.fwd_rev
      -- Use the product category structure
      exact Prod.ext (by
        have := congrArg Prod.fst i.fwd_rev
        exact this) (by
        have := congrArg Prod.snd i.fwd_rev
        exact this)
        |>.1
    · have := i.rev_fwd
      exact Prod.ext (by
        have := congrArg Prod.fst i.rev_fwd
        exact this) (by
        have := congrArg Prod.snd i.rev_fwd
        exact this)
        |>.1
  · apply hMd
    refine {
      fwd := ProdHom.snd i.fwd
      rev := ProdHom.snd i.rev
      fwd_rev := ?_
      rev_fwd := ?_
    }
    · have := congrArg Prod.snd i.fwd_rev; exact this
    · have := congrArg Prod.snd i.rev_fwd; exact this

/-! ## Product Factorization System -/

/--
Given factorization systems on C and D, construct one on C × D.
-/
def FactorizationSystem.prod {C D : Category}
    (fsC : FactorizationSystem C) (fsD : FactorizationSystem D) :
    FactorizationSystem (C ×ᶜ D) where
  E := fsC.E ×ₘ fsD.E
  M := fsC.M ×ₘ fsD.M
  factorization := by
    intro X Y f
    rcases fsC.factorization (ProdHom.fst f) with ⟨ZF, eC, mC, heC, hmC, hcompC⟩
    rcases fsD.factorization (ProdHom.snd f) with ⟨ZG, eD, mD, heD, hmD, hcompD⟩
    refine ⟨(ZF, ZG), (eC, eD), (mC, mD), ⟨heC, heD⟩, ⟨hmC, hmD⟩, ?_⟩
    ext
    · exact hcompC
    · exact hcompD
  orthogonal := by
    intro A B X Y e m he hm u v hsq
    rcases he with ⟨heC, heD⟩
    rcases hm with ⟨hmC, hmD⟩
    have hsqC : C.comp (ProdHom.fst m) (ProdHom.fst u) = C.comp (ProdHom.fst v) (ProdHom.fst e) :=
      congrArg Prod.fst hsq
    have hsqD : D.comp (ProdHom.snd m) (ProdHom.snd u) = D.comp (ProdHom.snd v) (ProdHom.snd e) :=
      congrArg Prod.snd hsq
    rcases fsC.orthogonal (ProdHom.fst e) (ProdHom.fst m) heC hmC
      (ProdHom.fst u) (ProdHom.fst v) hsqC with ⟨dC, hdCe, hmCdC⟩
    rcases fsD.orthogonal (ProdHom.snd e) (ProdHom.snd m) heD hmD
      (ProdHom.snd u) (ProdHom.snd v) hsqD with ⟨dD, hdDe, hmDdD⟩
    refine ⟨(dC, dD), ?_, ?_⟩
    · ext; exact hdCe; exact hdDe
    · ext; exact hmCdC; exact hmDdD
  containsIso_e := by
    intro X Y i
    apply MorphismClass.prod_containsIso (fsC.E) (fsD.E) fsC.containsIso_e fsD.containsIso_e i
  containsIso_m := by
    intro X Y i
    apply MorphismClass.prod_containsIso (fsC.M) (fsD.M) fsC.containsIso_m fsD.containsIso_m i

/-! ## Lifting in Product Categories -/

/-- The lifting property in a product category decomposes into components. -/
theorem HasLLP.prod {C D : Category} {A B X Y : (C ×ᶜ D).Obj}
    (e : (C ×ᶜ D)[A, B]) (m : (C ×ᶜ D)[X, Y])
    (heC : HasLLP (ProdHom.fst e) (ProdHom.fst m))
    (heD : HasLLP (ProdHom.snd e) (ProdHom.snd m)) : HasLLP e m := by
  intro u v hsq
  have hsqC : C.comp (ProdHom.fst m) (ProdHom.fst u) = C.comp (ProdHom.fst v) (ProdHom.fst e) :=
    congrArg Prod.fst hsq
  have hsqD : D.comp (ProdHom.snd m) (ProdHom.snd u) = D.comp (ProdHom.snd v) (ProdHom.snd e) :=
    congrArg Prod.snd hsq
  rcases heC (ProdHom.fst u) (ProdHom.fst v) hsqC with ⟨dC, hdCe, hmCdC⟩
  rcases heD (ProdHom.snd u) (ProdHom.snd v) hsqD with ⟨dD, hdDe, hmDdD⟩
  refine ⟨(dC, dD), ?_, ?_⟩
  · ext; exact hdCe; exact hdDe
  · ext; exact hmCdC; exact hmDdD

/-! ## Lifting Product -/

/-- The product of two lifting systems produces a lifting system on the product category. -/
def LiftingSystem.prod {C D : Category} (lsC : LiftingSystem C) (lsD : LiftingSystem D) :
    LiftingSystem (C ×ᶜ D) where
  L := lsC.L ×ₘ lsD.L
  R := lsC.R ×ₘ lsD.R
  lifting := by
    intro A B X Y e m he hm
    rcases he with ⟨heC, heD⟩
    rcases hm with ⟨hmC, hmD⟩
    exact HasLLP.prod e m
      (lsC.lifting (ProdHom.fst e) (ProdHom.fst m) heC hmC)
      (lsD.lifting (ProdHom.snd e) (ProdHom.snd m) heD hmD)

#eval "Constructions.Products: ProdHom.fst/snd/mk, MorphismClass.prod, FactorizationSystem.prod, HasLLP.prod, LiftingSystem.prod"
#eval "Product factorization decomposes: (E_C × E_D, M_C × M_D) on C × D"
#eval "Product lifting: LS_C × LS_D = (L_C × L_D, R_C × R_D)"
