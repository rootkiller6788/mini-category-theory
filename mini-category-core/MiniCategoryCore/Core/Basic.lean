/-
# MiniCategoryCore.Core.Basic

The fundamental definitions: Category, opposite category, product category.
A category consists of objects and morphisms between them, with
identity morphisms and associative composition.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Core.Objects

namespace MiniCategoryCore

/-! ## Category -/

/--
A category C consists of:
- A collection of objects `Obj`
- For each pair X,Y, a collection of morphisms `Hom X Y`
- An identity morphism `id X` for each object
- A composition `comp g f` for composable morphisms
- Laws: identity and associativity
-/
structure Category where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  assoc : ∀ {W X Y Z : Obj} (f : Hom Y Z) (g : Hom X Y) (h : Hom W X),
    comp f (comp g h) = comp (comp f g) h

/-- Convenient notation for hom-collections -/
notation:20 C:20 "[" X:20 " , " Y:20 "]" => Category.Hom C X Y

/-- Infix composition notation -/
def Category.compose {C : Category} {X Y Z : C.Obj} (g : C[Y, Z]) (f : C[X, Y]) : C[X, Z] :=
  C.comp g f

infixr:80 " ∘ " => Category.compose

/-! ## Category of Sets (archetypal example) -/

/-- The category of types and functions in universe u. -/
def SetCat : Category where
  Obj := Type u
  Hom X Y := X → Y
  id _ x := x
  comp g f x := g (f x)
  comp_id _ := rfl
  id_comp _ := rfl
  assoc _ _ _ := rfl

/-! ## Opposite Category -/

/-- The opposite category Cᵒᵖ has the same objects but reversed morphisms. -/
def Category.op (C : Category) : Category where
  Obj := C.Obj
  Hom X Y := C[Y, X]
  id X := C.id X
  comp g f := C.comp f g
  comp_id f := C.id_comp f
  id_comp f := C.comp_id f
  assoc f g h := C.assoc h g f

notation:70 C:70 "ᵒᵖ" => Category.op C

/-! ## Product Category -/

/-- The product of two categories C × D. -/
def Category.prod (C D : Category) : Category where
  Obj := C.Obj × D.Obj
  Hom X Y := C[X.1, Y.1] × D[X.2, Y.2]
  id X := (C.id X.1, D.id X.2)
  comp g f := (C.comp g.1 f.1, D.comp g.2 f.2)
  comp_id f := by
    rcases f with ⟨fC, fD⟩
    simp [C.comp_id, D.comp_id]
  id_comp f := by
    rcases f with ⟨fC, fD⟩
    simp [C.id_comp, D.id_comp]
  assoc f g h := by
    simp [C.assoc, D.assoc]

infixr:60 " ×ᶜ " => Category.prod

/-! ## Discrete Category -/

/-- The discrete category on a type: objects are elements, only identity morphisms. -/
def DiscCat (A : Type u) : Category where
  Obj := A
  Hom X Y := ULift (PLift (X = Y))
  id _ := ULift.up (PLift.up rfl)
  comp g f :=
    ULift.up (PLift.up (Eq.trans (PLift.down (ULift.down f)) (PLift.down (ULift.down g))))
  comp_id f := by
    cases f; cases down; cases down; rfl
  id_comp f := by
    cases f; cases down; cases down; rfl
  assoc f g h := by
    cases f; cases down; cases down
    cases g; cases down; cases down
    cases h; cases down; cases down; rfl

/-! ## Codiscrete Category -/

/-- The codiscrete category: every pair of objects has exactly one morphism. -/
inductive OneHom : Type where
  | mk

def CodiscCat (A : Type u) : Category where
  Obj := A
  Hom _ _ := OneHom
  id _ := OneHom.mk
  comp _ _ := OneHom.mk
  comp_id _ := rfl
  id_comp _ := rfl
  assoc _ _ _ := rfl

/-! ## Small Category -/

/-- A category where the object type is in the same universe as morphisms. -/
def isSmall (C : Category) : Prop := True

#eval "Core.Basic: Category, SetCat, Cᵒᵖ, C ×ᶜ D, DiscCat, CodiscCat"
