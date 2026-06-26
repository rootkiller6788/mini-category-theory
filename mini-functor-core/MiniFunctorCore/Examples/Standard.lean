/-
# MiniFunctorCore.Examples.Standard

Standard examples: SetCat functors, forgetful functors,
and basic presheaf examples.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Constructions.Products
import MiniFunctorCore.Properties.Invariants

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Forgetful Functors -/

/--
The forgetful functor from a category of structured sets to Set.
(This is a template; instantiate with concrete structures.)
-/
def forgetfulFunctor (C : Category) [h : C.Obj → Type u] : Functor C SetCat where
  mapObj X := Unit
  mapHom f x := x
  preservesId X := rfl
  preservesComp f g := rfl

/-! ## Identity Functor as Example -/

/--
The identity functor on SetCat is a basic example in the functor category [Set, Set].
-/
def idSetFunctor : Functor SetCat SetCat := Functor.id SetCat

#eval s!"Identity functor on SetCat: {idSetFunctor}"

/-! ## Constant Functor -/

/--
The constant functor to a fixed type.
-/
def constNatFunctor : Functor SetCat SetCat :=
  Functor.const SetCat SetCat Nat

#eval s!"Constant functor to Nat defined"

/-! ## Hom-Functor Example -/

/--
The covariant hom-functor Set(1, -) sends X to Hom(Unit, X) ≅ X.
-/
def homUnitFunctor : Functor SetCat SetCat :=
  homFunctor SetCat Unit

#eval s!"Hom-functor Set(Unit, -) defined"

/-! ## Contravariant Hom-Functor Example -/

/--
The contravariant hom-functor Set(-, Bool) sends X to Hom(X, Bool) = 2^X.
-/
def homBoolOpFunctor : Functor (SetCatᵒᵖ) SetCat :=
  homFunctorOp SetCat Bool

#eval s!"Hom-functor Set(-, Bool) defined"

/-! ## Functor Category Example -/

/--
The functor category [Discrete(2), Set] is equivalent to Set × Set.
-/
def twoObjDiscCat : Category := DiscCat (Fin 2)

def functorCatExample : Category := [twoObjDiscCat, SetCat]

#eval s!"Functor category [2, Set] ≅ Set × Set defined"

/-! ## Presheaf Examples -/

/--
The constant presheaf on C with value A.
-/
def constantPresheaf (C : Category) (A : Type u) : Functor (Cᵒᵖ) SetCat :=
  Functor.const (Cᵒᵖ) SetCat A

/--
The representable presheaf yX = C(-, X).
-/
def representablePresheaf (C : Category) (X : C.Obj) : Functor (Cᵒᵖ) SetCat :=
  homFunctorOp C X

#eval s!"Representable presheaf yX defined"

/-! ## Slice Category Example -/

/--
The slice category Set/X of types over X.
-/
def setSliceCat (X : Type u) : Category := SliceCat SetCat X

#eval s!"Slice category Set/X defined"

/-! ## Arrow Category Example -/

/--
The arrow category Set^→ of functions between types.
-/
def setArrowCat : Category := ArrowCat SetCat

#eval s!"Arrow category Set^→ defined"

#eval "Examples.Standard: forgetfulFunctor, idSetFunctor, constNatFunctor, homUnitFunctor, homBoolOpFunctor, functorCatExample, constantPresheaf, representablePresheaf, setSliceCat, setArrowCat"
