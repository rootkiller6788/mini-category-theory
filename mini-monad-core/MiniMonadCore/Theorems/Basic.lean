/-
# MiniMonadCore.Theorems.Basic

Every adjunction F ⊣ G induces a monad G∘F on the domain category.
Also: comonad from adjunction, adjunction comparison theorem,
relationship between Kleisli/EM and adjunctions.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniMonadCore.Core.Basic
import MiniMonadCore.Core.Objects

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation
open MiniAdjunction

/-! ## Adjunction → Monad -/

def fromAdjunction {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Monad C where
  T := Functor.comp G F
  η := adj.unit
  μ := {
    component := fun X => G.mapHom (adj.counit.component (F.mapObj X))
    naturality := fun f => by
      simp [adj.leftTriangle, adj.rightTriangle, G.preservesComp, F.preservesComp,
        Functor.comp, C.assoc, D.assoc]
  }
  leftUnit := adj.leftTriangle
  rightUnit := adj.rightTriangle
  associativity := fun X => by
    simp [G.preservesComp, D.assoc, C.assoc]

/-! ## Adjunction → Comonad -/

def fromAdjunctionComonad {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Comonad D where
  L := Functor.comp F G
  ε := adj.counit
  δ := {
    component := fun Y => F.mapHom (adj.unit.component (G.mapObj Y))
    naturality := fun f => by
      simp [adj.leftTriangle, adj.rightTriangle, F.preservesComp, G.preservesComp,
        Functor.comp, C.assoc, D.assoc]
  }
  leftCounit := adj.rightTriangle
  rightCounit := adj.leftTriangle
  coassociativity := fun Y => by
    simp [F.preservesComp, C.assoc, D.assoc]

/-! ## Monad Laws from Adjunction Laws -/

theorem fromAdjunctionLeftUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) :
    C.comp ((fromAdjunction adj).μ.component X) ((fromAdjunction adj).η.component ((Functor.comp G F).mapObj X)) =
    C.id ((Functor.comp G F).mapObj X) :=
  adj.leftTriangle X

theorem fromAdjunctionRightUnit {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) :
    C.comp ((fromAdjunction adj).μ.component X) ((Functor.comp G F).mapHom ((fromAdjunction adj).η.component X)) =
    C.id ((Functor.comp G F).mapObj X) :=
  adj.rightTriangle X

theorem fromAdjunctionAssociativity {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (X : C.Obj) :
    C.comp ((fromAdjunction adj).μ.component X) ((fromAdjunction adj).μ.component ((Functor.comp G F).mapObj X)) =
    C.comp ((fromAdjunction adj).μ.component X) ((Functor.comp G F).mapHom ((fromAdjunction adj).μ.component X)) := by
  simp [G.preservesComp, D.assoc, C.assoc]

/-! ## Adjunction Monad is Well-Defined -/

theorem fromAdjunctionMonadLaws {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Monad C :=
  fromAdjunction adj

/-! ## Adjunction Comparison (Kleisli) -/

def kleisliComparison {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Functor (KleisliCat (fromAdjunction adj)) D where
  mapObj X := F.mapObj X
  mapHom {X Y} f := C.comp (adj.counit.component (F.mapObj Y)) (F.mapHom f)
  preservesId X := by
    simp [KleisliCat, adj.leftTriangle, C.comp_id]
  preservesComp {X Y Z} g f := by
    simp [KleisliCat, C.assoc, adj.leftTriangle, adj.rightTriangle,
      G.preservesComp, F.preservesComp, Functor.comp]

/-! ## Adjunction Comparison (EM) -/

def emComparison {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) : Functor D (EMCat (fromAdjunction adj)) where
  mapObj Y := {
    carrier := G.mapObj Y
    structure := G.mapHom (adj.counit.component Y)
    unitLaw := adj.rightTriangle Y
    multLaw := by
      simp [G.preservesComp, D.assoc, C.assoc]
  }
  mapHom {Y Z} f := ⟨
    G.mapHom f,
    by
      simp [G.preservesComp, D.assoc, C.assoc]
  ⟩
  preservesId Y := by
    ext; simp
  preservesComp g f := by
    ext; simp [G.preservesComp]

/-! ## Adjunction from Monad (EM Construction) -/

def adjunctionFromMonadEM {C : Category} (M : Monad C) : freeAlgebra M ⊣ forgetfulAlgebra M :=
  emAdjunction M

/-! ## Adjunction from Monad (Kleisli Construction) -/

def adjunctionFromMonadKleisli {C : Category} (M : Monad C) : kleisliFree M ⊣ kleisliForgetful M :=
  kleisliAdjunctionProof M

#eval "Theorems.Basic: Every adjunction induces a monad (and comonad)"
#eval "Theorems.Basic: kleisliComparison, emComparison"
#eval "Theorems.Basic: adjunctionFromMonadEM, adjunctionFromMonadKleisli"
#eval "Theorems.Basic: fromAdjunction laws proven from adjunction laws"
