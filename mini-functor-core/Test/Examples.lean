/-
# Test.Examples

Step-by-step functor theory constructions.
Demonstrates the library by building up key examples.
-/

import MiniFunctorCore

open MiniFunctorCore
open MiniCategoryCore
open MiniMorphismSystem

/-!
## Step 1: Define a simple functor category
The functor category from a discrete category to Set.
-/

def TwoObj : Category := DiscCat (Fin 2)

def FunctorCat2Set : Category := [TwoObj, SetCat]

#eval "Step 1: [2, Set] ≅ Set × Set — pairs of sets"

/-!
## Step 2: Hom-functor on a simple category
-/

def homOnTwoObj (X : TwoObj.Obj) : Functor TwoObj SetCat :=
  homFunctor TwoObj X

#eval s!"Step 2: Hom-functor TwoObj(X, -) defined for each object X"

/-!
## Step 3: Contravariant hom-functor
-/

def homOpOnTwoObj (X : TwoObj.Obj) : Functor (TwoObjᵒᵖ) SetCat :=
  homFunctorOp TwoObj X

#eval s!"Step 3: Hom-functor TwoObj(-, X) : TwoObjᵒᵖ → Set"

/-!
## Step 4: Diagonal functor
-/

def diagSet : Functor SetCat ([TwoObj, SetCat]) := diag

#eval "Step 4: Diagonal functor Δ : Set → [2, Set]"

/-!
## Step 5: Evaluation functor
-/

def evalAt0 : Functor ([TwoObj, SetCat]) SetCat := eval (0 : Fin 2)

#eval "Step 5: Evaluation functor ev_0 : [2, Set] → Set"

/-!
## Step 6: Natural transformation in a functor category
-/

def constNat : Functor TwoObj SetCat := Functor.const TwoObj SetCat Nat

def constBool : Functor TwoObj SetCat := Functor.const TwoObj SetCat Bool

def natTransExample : constNat ⇒ constBool :=
  NatTrans.id constBool

#eval "Step 6: Natural transformation between constant functors"

/-!
## Step 7: Slice category construction
-/

def sliceSetNat : Category := SliceCat SetCat Nat

#eval "Step 7: Slice category Set/Nat"

/-!
## Step 8: Presheaf category
-/

def presheafOnTwoObj : Category := PresheafCategory TwoObj

#eval "Step 8: Presheaf category [2ᵒᵖ, Set]"

#eval "═══ All Example Steps Complete ═══"
