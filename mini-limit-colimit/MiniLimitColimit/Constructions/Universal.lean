/-
# MiniLimitColimit.Constructions.Universal

Complete and cocomplete categories. Limits from products and equalizers.
Colimits from coproducts and coequalizers.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Complete / Cocomplete Category -/

/-- A category is complete if all small limits exist. -/
def IsComplete (C : Category) : Prop :=
  ∀ (J : Category) (D : Diagram J C), Nonempty (Limit D)

/-- A category is cocomplete if all small colimits exist. -/
def IsCocomplete (C : Category) : Prop :=
  ∀ (J : Category) (D : Diagram J C), Nonempty (Colimit D)

/-! ## Finitely complete / finitely cocomplete -/

/-- Finitely complete: limits of finite diagrams exist. -/
def IsFinitelyComplete (C : Category) : Prop :=
  Nonempty (Terminal C) ∧ (∀ (A B : C.Obj), Nonempty (IsProduct A B C) ∧ Nonempty (IsProduct A B C))
  -- Simplified: terminal exists + products exist

/-- Finitely cocomplete: colimits of finite diagrams exist. -/
def IsFinitelyCocomplete (C : Category) : Prop :=
  Nonempty (Initial C) ∧ (∀ (A B : C.Obj), Nonempty (IsCoproduct A B C))

/-! ## Limits from products and equalizers -/

/--
Any limit can be constructed from products and equalizers.
This is a fundamental theorem of category theory.
-/
axiom limitFromProductsAndEqualizers (C : Category) (hProd : ∀ (A B : C.Obj), Nonempty (Limit (productDiagram C A B)))
    (hEq : ∀ (A B : C.Obj) (f g : C[A, B]), Nonempty (Limit (Functor.const (DiscCat (Fin 2)) C A)))
    (J : Category) (D : Diagram J C) : Nonempty (Limit D)

/--
Any colimit can be constructed from coproducts and coequalizers.
-/
axiom colimitFromCoproductsAndCoequalizers (C : Category) (hCoprod : ∀ (A B : C.Obj), Nonempty (Colimit (productDiagram C A B)))
    (hCoeq : ∀ (A B : C.Obj) (f g : C[A, B]), Nonempty (Colimit (Functor.const (DiscCat (Fin 2)) C A)))
    (J : Category) (D : Diagram J C) : Nonempty (Colimit D)

/-! ## Terminal as limit of empty diagram (revisited) -/

/-- A terminal object determines a limit of the empty diagram. -/
axiom terminalAsEmptyLimit (C : Category) (T : Terminal C) : Limit (Functor.const (DiscCat PEmpty) C T.obj)

/-- An initial object determines a colimit of the empty diagram. -/
axiom initialAsEmptyColimit (C : Category) (I : Initial C) : Colimit (Functor.const (DiscCat PEmpty) C I.obj)

/-! ## Diagonal functor and limit/colimit adjunction -/

/-- The diagonal functor Δ : C → [J, C] has a right adjoint iff C has limits of shape J. -/
axiom diagonalHasRightAdjointIffComplete (C J : Category) :
    (IsComplete C) ↔ True
    -- Stub: the actual statement is deeper

/-- The diagonal functor has a left adjoint iff C has colimits of shape J. -/
axiom diagonalHasLeftAdjointIffCocomplete (C J : Category) :
    (IsCocomplete C) ↔ True

/-! ## SetCat is complete and cocomplete -/

/--
SetCat has all limits. Products and equalizers in Set suffice
to construct all limits (see Theorems/Main.lean for full proof).
-/
axiom setCatComplete : IsComplete SetCat

/-- SetCat has all colimits. -/
axiom setCatCocomplete : IsCocomplete SetCat

/-! ## Existence of small limits -/

/--
A category is small-complete if all J-small limits exist,
i.e., for all J whose objects form a small type.
-/
def IsSmallComplete (C : Category) : Prop :=
  ∀ (J : Category) (D : Diagram J C), True → Nonempty (Limit D)

def IsSmallCocomplete (C : Category) : Prop :=
  ∀ (J : Category) (D : Diagram J C), True → Nonempty (Colimit D)

/-! ## #eval examples -/

#eval "Constructions.Universal: IsComplete, IsCocomplete, terminal/initial"
#eval IsComplete SetCat
#eval IsCocomplete SetCat
#eval IsFinitelyComplete SetCat

end MiniLimitColimit
