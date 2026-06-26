/-
# MiniFunctorCore.Core.Basic

Functor categories, the category of functors [C, D], and
the hom-functor construction.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Morphisms.Hom

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Functor Category [C, D] -/

/--
The functor category [C, D] whose objects are functors F : C → D
and morphisms are natural transformations.
-/
def FunctorCategory (C D : Category) : Category where
  Obj := Functor C D
  Hom F G := ∀ (X : C.Obj), D[F.mapObj X, G.mapObj X]
  id F X := D.id (F.mapObj X)
  comp β α X := D.comp (β X) (α X)
  comp_id f := by
    funext X; apply D.comp_id
  id_comp f := by
    funext X; apply D.id_comp
  assoc f g h := by
    funext X; apply D.assoc

notation:60 "[" C:60 " , " D:60 "]" => FunctorCategory C D

/-! ## Hom-Functor -/

/--
The covariant hom-functor C(X, -) : C → Set.
Given an object X of C, this sends each Y to Hom(X, Y).
-/
def homFunctor (C : Category) (X : C.Obj) : Functor C SetCat where
  mapObj Y := C[X, Y]
  mapHom f g := C.comp f g
  preservesId Y := by
    funext g; simp [C.id_comp]
  preservesComp f g := by
    funext h; simp [C.assoc]

/-! ## Contravariant Hom-Functor -/

/--
The contravariant hom-functor C(-, X) : Cᵒᵖ → Set.
Given an object X of C, this sends Y to Hom(Y, X).
-/
def homFunctorOp (C : Category) (X : C.Obj) : Functor (Cᵒᵖ) SetCat where
  mapObj Y := C[Y, X]
  mapHom f g := C.comp g f
  preservesId Y := by
    funext g; simp [C.comp_id]
  preservesComp f g := by
    funext h; simp [C.assoc]

/-! ## Diagonal Functor -/

/--
The diagonal functor Δ : D → [C, D] sends each object to the constant functor
and each morphism to the constant natural transformation.
-/
def diag {C D : Category} : Functor D ([C, D]) where
  mapObj Y := Functor.const C D Y
  mapHom f X := f
  preservesId Y := by
    funext X; simp [Functor.const]
  preservesComp f g := by
    funext X; simp [Functor.const]

/-! ## Evaluation Functor -/

/--
The evaluation functor ev_X : [C, D] → D evaluates a functor at a fixed object X.
-/
def eval {C D : Category} (X : C.Obj) : Functor ([C, D]) D where
  mapObj F := F.mapObj X
  mapHom η := η X
  preservesId F := rfl
  preservesComp _ _ := rfl

/-! ## Slice Category -/

/--
A slice object over X: an object A together with a morphism A → X.
-/
structure SliceObj (C : Category) (X : C.Obj) where
  obj : C.Obj
  arr : C[obj, X]

/--
The slice category C/X: objects are morphisms into X,
morphisms are commuting triangles.
-/
def SliceCat (C : Category) (X : C.Obj) : Category where
  Obj := SliceObj C X
  Hom A B := { f : C[A.obj, B.obj] // C.comp B.arr f = A.arr }
  id A := ⟨C.id A.obj, by simp [C.id_comp]⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    simp [C.assoc, hf, hg]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

/-! ## Coslice Category -/

/--
A coslice object under X: an object A together with a morphism X → A.
-/
structure CosliceObj (C : Category) (X : C.Obj) where
  obj : C.Obj
  arr : C[X, obj]

/--
The coslice category X/C: objects are morphisms out of X,
morphisms are commuting triangles.
-/
def CosliceCat (C : Category) (X : C.Obj) : Category where
  Obj := CosliceObj C X
  Hom A B := { f : C[A.obj, B.obj] // C.comp f A.arr = B.arr }
  id A := ⟨C.id A.obj, by simp [C.comp_id]⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    simp [C.assoc, hf, hg]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  assoc f g h := by simp [C.assoc]

/-! ## Arrow Category -/

/--
The arrow category C^→: objects are morphisms of C,
morphisms are commutative squares.
-/
def ArrowCat (C : Category) : Category where
  Obj := Σ (X Y : C.Obj), C[X, Y]
  Hom A B := { f : (C[A.1, B.1] × C[A.2.1, B.2.1]) // C.comp B.2.2 f.1 = C.comp f.2 A.2.2 }
  id A := ⟨(C.id A.1, C.id A.2.1), by simp⟩
  comp g f :=
    let gf1 := C.comp g.1.1 f.1.1
    let gf2 := C.comp g.1.2 f.1.2
    ⟨(gf1, gf2), by
      rcases g with ⟨⟨g1, g2⟩, hg⟩
      rcases f with ⟨⟨f1, f2⟩, hf⟩
      simp [C.assoc, hf, hg]⟩
  comp_id f := by rcases f with ⟨⟨f1, f2⟩, hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨⟨f1, f2⟩, hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

/-! ## Presheaf Category -/

/--
A presheaf on C is a functor Cᵒᵖ → Set.
The presheaf category is the functor category [Cᵒᵖ, Set].
-/
def PresheafCategory (C : Category) : Category := [Cᵒᵖ, SetCat]

/-! ## Twisted Arrow Category -/

/--
The twisted arrow category Tw(C): objects are morphisms f : A → B,
morphisms (u, v) : f → g are factorizations g ∘ u = v ∘ f.
-/
structure TwistedArrow (C : Category) where
  src : C.Obj
  tgt : C.Obj
  arr : C[src, tgt]

def TwistedArrowCat (C : Category) : Category where
  Obj := TwistedArrow C
  Hom f g := { p : C[g.src, f.src] × C[f.tgt, g.tgt] //
    C.comp g.arr p.1 = C.comp p.2 f.arr }
  id f := ⟨(C.id f.src, C.id f.tgt), by simp⟩
  comp βα αβ :=
    let u := C.comp βα.1.1 αβ.1.1
    let v := C.comp βα.1.2 αβ.1.2
    ⟨(u, v), by
      rcases βα with ⟨⟨u2, v2⟩, h2⟩
      rcases αβ with ⟨⟨u1, v1⟩, h1⟩
      simp [C.assoc, h1, h2]⟩
  comp_id f := by rcases f with ⟨⟨f1, f2⟩, hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨⟨f1, f2⟩, hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

#eval "Core.Basic: FunctorCategory [C,D], homFunctor, homFunctorOp, diag, eval, SliceCat, CosliceCat, ArrowCat, PresheafCategory, TwistedArrowCat"
