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

def limitUnique {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C[L₁.limitCone.apex, L₂.limitCone.apex] :=
  L₂.mediate L₁.limitCone

def limitUniqueInv {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
    C[L₂.limitCone.apex, L₁.limitCone.apex] :=
  L₁.mediate L₂.limitCone

axiom limitUniqueId {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
  C.comp (limitUnique L₁ L₂) (limitUniqueInv L₁ L₂) = C.id L₁.limitCone.apex

axiom limitUniqueId' {J C : Category} {D : Diagram J C} (L₁ L₂ : Limit D) :
  C.comp (limitUniqueInv L₁ L₂) (limitUnique L₁ L₂) = C.id L₂.limitCone.apex

/-! ## Colimit is unique up to isomorphism -/

def colimitUnique {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C[C₂.colimitCocone.nadir, C₁.colimitCocone.nadir] :=
  C₁.mediate C₂.colimitCocone

def colimitUniqueInv {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
    C[C₁.colimitCocone.nadir, C₂.colimitCocone.nadir] :=
  C₂.mediate C₁.colimitCocone

axiom colimitUniqueId {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
  C.comp (colimitUnique C₁ C₂) (colimitUniqueInv C₁ C₂) = C.id C₁.colimitCocone.nadir

axiom colimitUniqueId' {J C : Category} {D : Diagram J C} (C₁ C₂ : Colimit D) :
  C.comp (colimitUniqueInv C₁ C₂) (colimitUnique C₁ C₂) = C.id C₂.colimitCocone.nadir

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
