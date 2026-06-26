/-
# MiniNaturalTransformation.Core.Basic

Natural transformations between functors. Core definitions: structure,
component access, vertical composition. Also provides shared concrete
functors for examples across the library.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects

namespace MiniNaturalTransformation

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Natural Transformation -/

structure NaturalTransformation {C D : Category} (F G : Functor C D) where
  component : ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]
  naturality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (F.mapHom f) = D.comp (G.mapHom f) (component X)

notation:50 F:50 " ⇒ " G:50 => NaturalTransformation F G

def NaturalTransformation.at {C D : Category} {F G : Functor C D}
    (η : F ⇒ G) (X : C.Obj) : D[F.mapObj X, G.mapObj X] := η.component X

/-! ## Vertical Composition -/

def NaturalTransformation.vcomp {C D : Category} {F G H : Functor C D}
    (μ : G ⇒ H) (η : F ⇒ G) : F ⇒ H where
  component X := D.comp (μ.component X) (η.component X)
  naturality f := by
    calc
      D.comp (D.comp (μ.component _) (η.component _)) (F.mapHom f) = _ := rfl
      _ = D.comp (μ.component _) (D.comp (η.component _) (F.mapHom f)) := by
        rw [D.assoc]
      _ = D.comp (μ.component _) (D.comp (G.mapHom f) (η.component _)) := by
        rw [η.naturality]
      _ = D.comp (D.comp (μ.component _) (G.mapHom f)) (η.component _) := by
        rw [← D.assoc]
      _ = D.comp (D.comp (H.mapHom f) (μ.component _)) (η.component _) := by
        rw [μ.naturality]
      _ = D.comp (H.mapHom f) (D.comp (μ.component _) (η.component _)) := by
        rw [D.assoc]

/-! ## Shared Concrete Functors for Examples -/

/-- List functor on SetCat: X → List X, map via List.map. -/
def listFunctor : Functor SetCat SetCat where
  mapObj X := List X
  mapHom f := List.map f
  preservesId _ := by funext x; simp
  preservesComp _ _ := by funext x; simp

/-- Option/Maybe functor on SetCat: X → Option X, map via Option.map. -/
def maybeFunctor : Functor SetCat SetCat where
  mapObj X := Option X
  mapHom f := Option.map f
  preservesId _ := by funext x; simp
  preservesComp _ _ := by funext x; simp

/-- Identity functor on SetCat. -/
def idFunctor : Functor SetCat SetCat := Functor.id SetCat

/-- Constant functor at Nat on SetCat. -/
def constNat : Functor SetCat SetCat := Functor.const SetCat SetCat Nat

/-- Powerset functor on SetCat: X → (X → Prop), existential image. -/
def powersetFunctor : Functor SetCat SetCat where
  mapObj X := X → Prop
  mapHom {X Y} f P y := ∃ x, f x = y ∧ P x
  preservesId X := by
    funext P; ext y; constructor
    · intro ⟨x, hx, hP⟩; subst hx; exact hP
    · intro hP; exact ⟨y, rfl, hP⟩
  preservesComp {X Y Z} f g := by
    funext P; ext z; constructor
    · intro ⟨x, hx, hP⟩; exact ⟨g x, rfl, x, hx, hP⟩
    · intro ⟨y, hy, x, hx, hP⟩; subst hy; exact ⟨x, hx, hP⟩

#eval "Core.Basic: NaturalTransformation F ⇒ G, vertical composition, shared functors"
