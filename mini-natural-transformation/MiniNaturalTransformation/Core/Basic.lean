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

/-! ## Component-wise Equality -/

/--
Two natural transformations are equal if and only if they have equal
components at every object. This is the fundamental extensionality principle.
-/
theorem natTrans_ext {C D : Category} {F G : Functor C D} (α β : F ⇒ G) :
    α = β ↔ ∀ (X : C.Obj), α.component X = β.component X := by
  constructor
  · intro h X; rw [h]
  · intro h
    cases α; cases β
    simp at h
    simp [h]

/-! ## Natural Transformation Pre-composition with Functor -/

/--
Pre-composition of a natural transformation with a functor:
given η : F ⇒ G with F, G : D → E and H : C → D,
we get ηH : F∘H ⇒ G∘H with component η_{H(X)}.
-/
def NaturalTransformation.precomp {C D E : Category}
    (H : Functor C D) {F G : Functor D E} (η : F ⇒ G) :
    Functor.comp H F ⇒ Functor.comp H G where
  component X := η.component (H.mapObj X)
  naturality {X Y} f := by
    simp [η.naturality (H.mapHom f), H.preservesComp]

/-! ## Natural Transformation Post-composition with Functor -/

/--
Post-composition of a natural transformation with a functor:
given η : F ⇒ G with F, G : C → D and K : D → E,
we get Kη : K∘F ⇒ K∘G with component K(η_X).
-/
def NaturalTransformation.postcomp {C D E : Category}
    {F G : Functor C D} (η : F ⇒ G) (K : Functor D E) :
    Functor.comp F K ⇒ Functor.comp G K where
  component X := K.mapHom (η.component X)
  naturality {X Y} f := by
    have h := η.naturality f
    simp [← K.preservesComp, h, K.preservesComp]

/-! ## #eval Examples -/

/-- Singleton functor: X → {X}. -/
def singletonFunctor : Functor SetCat SetCat where
  mapObj X := X
  mapHom f x := f x
  preservesId _ := rfl
  preservesComp _ _ := rfl

#eval "Core.Basic: NaturalTransformation F ⇒ G, vertical composition, shared functors"
#eval "natTrans_ext: equality determined by components"
#eval "NaturalTransformation.precomp and postcomp operations defined"
