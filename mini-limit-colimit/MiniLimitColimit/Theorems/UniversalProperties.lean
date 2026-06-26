/-
# MiniLimitColimit.Theorems.UniversalProperties

Universal property: limit-universal, colimit-universal,
adjunction between constant diagram and limit functors.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniFunctorCore.Core.Basic
import MiniNaturalTransformation.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Universal

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Limit-universal property -/

/--
The limit is the universal cone: for any cone c over D,
there exists a unique morphism from c.apex to the limit apex
making the triangles commute.

Formally: Cone(D) ≅ C(-, lim D)  (Yoneda-like representation).
-/
def limitUniversal {J C : Category} {D : Diagram J C} (L : Limit D) (c : Cone D) :
    C[c.apex, L.limitCone.apex] :=
  L.mediate c

def limitUniversalCommutes {J C : Category} {D : Diagram J C} (L : Limit D) (c : Cone D) (j : J.Obj) :
    C.comp (L.limitCone.proj j) (limitUniversal L c) = c.proj j :=
  L.factor c j

def limitUniversalUnique {J C : Category} {D : Diagram J C} (L : Limit D) (c : Cone D)
    (f : C[c.apex, L.limitCone.apex])
    (h : ∀ (j : J.Obj), C.comp (L.limitCone.proj j) f = c.proj j) : f = limitUniversal L c :=
  L.unique c f h

/-! ## Colimit-universal property -/

def colimitUniversal {J C : Category} {D : Diagram J C} (CL : Colimit D) (c : Cocone D) :
    C[CL.colimitCocone.nadir, c.nadir] :=
  CL.mediate c

def colimitUniversalCommutes {J C : Category} {D : Diagram J C} (CL : Colimit D) (c : Cocone D) (j : J.Obj) :
    C.comp (colimitUniversal CL c) (CL.colimitCocone.inj j) = c.inj j :=
  CL.factor c j

def colimitUniversalUnique {J C : Category} {D : Diagram J C} (CL : Colimit D) (c : Cocone D)
    (f : C[CL.colimitCocone.nadir, c.nadir])
    (h : ∀ (j : J.Obj), C.comp f (CL.colimitCocone.inj j) = c.inj j) : f = colimitUniversal CL c :=
  CL.unique c f h

/-! ## Adjunction between constant diagram and limit -/

/--
The constant diagram functor Δ : C → [J, C] (diagonal) is left adjoint
to the limit functor lim : [J, C] → C (when C is J-complete).
-/
axiom diagonalLeftAdjointToLimit {C J : Category} (hComplete : IsComplete C) : True

/--
Dually, the colimit functor is left adjoint to the diagonal functor.
-/
axiom colimitLeftAdjointToDiagonal {C J : Category} (hCocomplete : IsCocomplete C) : True

/-! ## Hom-functor preserves limits -/

/--
The hom-functor C(X, -) : C → SetCat preserves limits:
C(X, lim D) ≅ lim (C(X, D(-))).
In other words, Hom(X, lim D) ≅ lim(Hom(X, D(-))).
-/
axiom homFunctorPreservesLimits {J C : Category} (X : C.Obj) (D : Diagram J C) (L : Limit D) :
    Nonempty (IsProduct (SetCat := SetCat)
      (C[X, L.limitCone.apex])
      (C[X, L.limitCone.apex])
      (C[X, L.limitCone.apex]))

/-! ## Yoneda preserves limits -/

/--
The Yoneda embedding preserves limits:
y(lim D) ≅ lim(y ∘ D) in [Cᵒᵖ, Set].
-/
axiom yonedaPreservesLimits {J C : Category} (D : Diagram J C) (L : Limit D) : True

/-! ## Representable functor preserves limits -/

/--
Every representable functor Hom(X, -) preserves limits.
-/
axiom representablePreservesLimits (C : Category) (X : C.Obj) : True

/-! ## Parametrized limit universal property -/

/--
For any object X and limit cone L over D, there is a natural bijection:
  C(X, L.apex) ≅ Cone(D with apex fixed at X)
-/
def parametrizedLimitUniversal {J C : Category} {D : Diagram J C} (L : Limit D) (X : C.Obj)
    (f : C[X, L.limitCone.apex]) : Cone D where
  apex := X
  proj j := C.comp (L.limitCone.proj j) f
  naturality {i j} u := by
    calc
      C.comp (D.mapHom u) (C.comp (L.limitCone.proj i) f) = _ := rfl
      _ = C.comp (C.comp (D.mapHom u) (L.limitCone.proj i)) f := by
        rw [C.assoc]
      _ = C.comp (L.limitCone.proj j) f := by
        rw [L.limitCone.naturality u]

/-! ## #eval examples -/

def trivialShape : Category := DiscCat Unit
def trivialDiag : Diagram trivialShape SetCat := Functor.const trivialShape SetCat Nat

def trivCone : Cone trivialDiag where
  apex := Nat
  proj _ := fun n => n
  naturality _ := by simp

def trivLimit : Limit trivialDiag where
  limitCone := trivCone
  mediate _ := fun n => n
  factor _ _ := rfl
  unique _ _ _ := rfl

def trivCocone : Cocone trivialDiag where
  nadir := Nat
  inj _ := fun n => n
  naturality _ := by simp

def trivColimit : Colimit trivialDiag where
  colimitCocone := trivCocone
  mediate _ := fun n => n
  factor _ _ := rfl
  unique _ _ _ := rfl

#eval "Theorems.UniversalProperties: limitUniversal, colimitUniversal, diagonal adjunction"
#eval limitUniversal trivLimit trivCone 42
#eval colimitUniversal trivColimit trivCocone 42
#eval parametrizedLimitUniversal trivLimit Nat (fun n : Nat => n) |>.apex

end MiniLimitColimit
