/-
# MiniLimitColimit.Core.Laws

Limit and colimit uniqueness laws, universal mapping property.
IsLimit and IsColimit as propositional predicates.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## IsLimit and IsColimit predicates -/

structure IsLimit {J C : Category} {D : Diagram J C} (c : Cone D) where
  mediate : ∀ (c' : Cone D), C[c'.apex, c.apex]
  factor : ∀ (c' : Cone D) (j : J.Obj),
    C.comp (c.proj j) (mediate c') = c'.proj j
  unique : ∀ (c' : Cone D) (f : C[c'.apex, c.apex]),
    (∀ (j : J.Obj), C.comp (c.proj j) f = c'.proj j) → f = mediate c'

structure IsColimit {J C : Category} {D : Diagram J C} (c : Cocone D) where
  mediate : ∀ (c' : Cocone D), C[c.nadir, c'.nadir]
  factor : ∀ (c' : Cocone D) (j : J.Obj),
    C.comp (mediate c') (c.inj j) = c'.inj j
  unique : ∀ (c' : Cocone D) (f : C[c.nadir, c'.nadir]),
    (∀ (j : J.Obj), C.comp f (c.inj j) = c'.inj j) → f = mediate c'

/-! ## Limit is unique up to isomorphism -/

/-- The canonical morphism from limit L₁ to limit L₂, induced by the universal property. -/
def limitUnique {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C[L₁.limitCone.apex, L₂.limitCone.apex] :=
  L₂.mediate L₁.limitCone

/-- The canonical morphism from limit L₂ to limit L₁, the inverse direction. -/
def limitUniqueInv {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C[L₂.limitCone.apex, L₁.limitCone.apex] :=
  L₁.mediate L₂.limitCone

/-- The mediating morphism from a limit cone to itself is the identity.
    This is a key lemma that falls out of the universal property. -/
theorem limit_mediate_self_id {J C : Category} {D : Diagram J C} (L : Limit D) :
    L.mediate L.limitCone = C.id L.limitCone.apex := by
  apply L.unique L.limitCone (C.id L.limitCone.apex)
  intro j
  exact C.comp_id (L.limitCone.proj j)

/-- The composition `limitUnique ∘ limitUniqueInv` equals the identity on L₂'s apex.
    This proves that limits of the same diagram are canonically isomorphic.
    Proof: apply the universal property twice — first via L₂.factor, then L₁.factor. -/
theorem limitUniqueId {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C.comp (limitUnique L₁ L₂) (limitUniqueInv L₁ L₂) = C.id L₂.limitCone.apex := by
  have h_eq : C.comp (limitUnique L₁ L₂) (limitUniqueInv L₁ L₂) = L₂.mediate L₂.limitCone := by
    apply L₂.unique L₂.limitCone (C.comp (limitUnique L₁ L₂) (limitUniqueInv L₁ L₂))
    intro j
    calc
      C.comp (L₂.limitCone.proj j) (C.comp (limitUnique L₁ L₂) (limitUniqueInv L₁ L₂))
          = C.comp (C.comp (L₂.limitCone.proj j) (limitUnique L₁ L₂)) (limitUniqueInv L₁ L₂) := by
        rw [C.assoc]
      _ = C.comp (L₁.limitCone.proj j) (limitUniqueInv L₁ L₂) := by
        rw [L₂.factor L₁.limitCone j]
      _ = C.comp (L₁.limitCone.proj j) (L₁.mediate L₂.limitCone) := rfl
      _ = L₂.limitCone.proj j := by
        rw [L₁.factor L₂.limitCone j]
  rw [h_eq, limit_mediate_self_id L₂]

/-- The composition `limitUniqueInv ∘ limitUnique` equals the identity on L₁'s apex.
    The symmetric counterpart, proved identically by exchanging L₁ and L₂. -/
theorem limitUniqueId' {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C.comp (limitUniqueInv L₁ L₂) (limitUnique L₁ L₂) = C.id L₁.limitCone.apex := by
  have h_eq : C.comp (limitUniqueInv L₁ L₂) (limitUnique L₁ L₂) = L₁.mediate L₁.limitCone := by
    apply L₁.unique L₁.limitCone (C.comp (limitUniqueInv L₁ L₂) (limitUnique L₁ L₂))
    intro j
    calc
      C.comp (L₁.limitCone.proj j) (C.comp (limitUniqueInv L₁ L₂) (limitUnique L₁ L₂))
          = C.comp (C.comp (L₁.limitCone.proj j) (limitUniqueInv L₁ L₂)) (limitUnique L₁ L₂) := by
        rw [C.assoc]
      _ = C.comp (L₂.limitCone.proj j) (limitUnique L₁ L₂) := by
        rw [L₁.factor L₂.limitCone j]
      _ = C.comp (L₂.limitCone.proj j) (L₂.mediate L₁.limitCone) := rfl
      _ = L₁.limitCone.proj j := by
        rw [L₂.factor L₁.limitCone j]
  rw [h_eq, limit_mediate_self_id L₁]

/-- Limits of the same diagram are isomorphic. Construct the Iso from the two
    mediating morphisms and the two identity proofs above. -/
def limitIso {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    Iso C L₁.limitCone.apex L₂.limitCone.apex where
  hom := limitUnique L₁ L₂
  inv := limitUniqueInv L₁ L₂
  hom_inv_id := limitUniqueId L₁ L₂
  inv_hom_id := limitUniqueId' L₁ L₂

/-! ## Colimit is unique up to isomorphism -/

/-- The canonical morphism from colimit C₂ to colimit C₁, induced by the universal property. -/
def colimitUnique {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C[C₂.colimitCocone.nadir, C₁.colimitCocone.nadir] :=
  C₁.mediate C₂.colimitCocone

/-- The canonical morphism from colimit C₁ to colimit C₂. -/
def colimitUniqueInv {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C[C₁.colimitCocone.nadir, C₂.colimitCocone.nadir] :=
  C₂.mediate C₁.colimitCocone

/-- The mediating morphism from a colimit cocone to itself is the identity. -/
theorem colimit_mediate_self_id {J C : Category} {D : Diagram J C} (CL : Colimit D) :
    CL.mediate CL.colimitCocone = C.id CL.colimitCocone.nadir := by
  apply CL.unique CL.colimitCocone (C.id CL.colimitCocone.nadir)
  intro j
  exact C.id_comp (CL.colimitCocone.inj j)

/-- The composition `colimitUnique ∘ colimitUniqueInv` = id on C₁'s nadir. -/
theorem colimitUniqueId {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C.comp (colimitUnique C₁ C₂) (colimitUniqueInv C₁ C₂) = C.id C₁.colimitCocone.nadir := by
  have h_eq : C.comp (colimitUnique C₁ C₂) (colimitUniqueInv C₁ C₂) = C₁.mediate C₁.colimitCocone := by
    apply C₁.unique C₁.colimitCocone (C.comp (colimitUnique C₁ C₂) (colimitUniqueInv C₁ C₂))
    intro j
    calc
      C.comp (C.comp (colimitUnique C₁ C₂) (colimitUniqueInv C₁ C₂)) (C₁.colimitCocone.inj j)
          = C.comp (colimitUnique C₁ C₂) (C.comp (colimitUniqueInv C₁ C₂) (C₁.colimitCocone.inj j)) := by
        rw [← C.assoc]
      _ = C.comp (colimitUnique C₁ C₂) (C₂.colimitCocone.inj j) := by
        rw [C₁.factor C₂.colimitCocone j]
      _ = C.comp (C₁.mediate C₂.colimitCocone) (C₂.colimitCocone.inj j) := rfl
      _ = C₁.colimitCocone.inj j := by
        rw [C₂.factor C₁.colimitCocone j]
  rw [h_eq, colimit_mediate_self_id C₁]

/-- The composition `colimitUniqueInv ∘ colimitUnique` = id on C₂'s nadir. -/
theorem colimitUniqueId' {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C.comp (colimitUniqueInv C₁ C₂) (colimitUnique C₁ C₂) = C.id C₂.colimitCocone.nadir := by
  have h_eq : C.comp (colimitUniqueInv C₁ C₂) (colimitUnique C₁ C₂) = C₂.mediate C₂.colimitCocone := by
    apply C₂.unique C₂.colimitCocone (C.comp (colimitUniqueInv C₁ C₂) (colimitUnique C₁ C₂))
    intro j
    calc
      C.comp (C.comp (colimitUniqueInv C₁ C₂) (colimitUnique C₁ C₂)) (C₂.colimitCocone.inj j)
          = C.comp (colimitUniqueInv C₁ C₂) (C.comp (colimitUnique C₁ C₂) (C₂.colimitCocone.inj j)) := by
        rw [← C.assoc]
      _ = C.comp (colimitUniqueInv C₁ C₂) (C₁.colimitCocone.inj j) := by
        rw [C₂.factor C₁.colimitCocone j]
      _ = C.comp (C₂.mediate C₁.colimitCocone) (C₁.colimitCocone.inj j) := rfl
      _ = C₂.colimitCocone.inj j := by
        rw [C₁.factor C₂.colimitCocone j]
  rw [h_eq, colimit_mediate_self_id C₂]

/-- Colimits of the same diagram are isomorphic. -/
def colimitIso {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    Iso C C₁.colimitCocone.nadir C₂.colimitCocone.nadir where
  hom := colimitUniqueInv C₁ C₂
  inv := colimitUnique C₁ C₂
  hom_inv_id := colimitUniqueId' C₁ C₂
  inv_hom_id := colimitUniqueId C₁ C₂

/-! ## Cone factorisation property -/

def limitConeFactorisation {J C : Category} {D : Diagram J C} (L : Limit D)
    (c : Cone D) (j : J.Obj) :
    C.comp (L.limitCone.proj j) (L.mediate c) = c.proj j :=
  L.factor c j

def colimitCoconeFactorisation {J C : Category} {D : Diagram J C} (CL : Colimit D)
    (c : Cocone D) (j : J.Obj) :
    C.comp (CL.mediate c) (CL.colimitCocone.inj j) = c.inj j :=
  CL.factor c j

/-! ## Limit from IsLimit -/

def limitFromIsLimit {J C : Category} {D : Diagram J C} (c : Cone D) (h : IsLimit c) : Limit D where
  limitCone := c
  mediate := h.mediate
  factor := h.factor
  unique := h.unique

def colimitFromIsColimit {J C : Category} {D : Diagram J C} (c : Cocone D) (h : IsColimit c) : Colimit D where
  colimitCocone := c
  mediate := h.mediate
  factor := h.factor
  unique := h.unique

/-! ## IsLimit from Limit -/

def isLimitOfLimit {J C : Category} {D : Diagram J C} (L : Limit D) : IsLimit L.limitCone where
  mediate := L.mediate
  factor := L.factor
  unique := L.unique

def isColimitOfColimit {J C : Category} {D : Diagram J C} (CL : Colimit D) : IsColimit CL.colimitCocone where
  mediate := CL.mediate
  factor := CL.factor
  unique := CL.unique

/-! ## #eval examples -/

def trivialIndex : Category := DiscCat Unit
def trivialDiagram : Diagram trivialIndex SetCat := Functor.const trivialIndex SetCat Unit

def trivialCone : Cone trivialDiagram where
  apex := Unit
  proj _ := id
  naturality _ := by
    simp [trivialIndex, DiscCat, trivialDiagram, Functor.const, SetCat]

def trivialIsLimit : IsLimit trivialCone where
  mediate c' := fun _ => ()
  factor c' j := rfl
  unique c' f _ := by
    funext x; simp

def trivialIsColimit : IsColimit
    { nadir := Unit
      inj _ := id
      naturality _ := by simp [SetCat]
    : Cocone trivialDiagram } where
  mediate c' := fun _ => ()
  factor c' j := rfl
  unique c' f _ := by
    funext x; simp

#eval "Core.Laws: IsLimit, IsColimit, limitUnique, colimitUnique"
#eval trivialIsLimit.mediate trivialCone ()
#eval limitConeFactorisation (limitFromIsLimit trivialCone trivialIsLimit) trivialCone ()

end MiniLimitColimit
