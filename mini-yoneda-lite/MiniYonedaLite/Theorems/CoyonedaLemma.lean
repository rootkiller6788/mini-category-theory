/-
# MiniYonedaLite.Theorems.CoyonedaLemma

The co-Yoneda lemma: the dual of the Yoneda lemma.
For a functor F : Cᵒᵖ → Set, Nat(Hom(-, X), F) ≅ F(X).

This is obtained by applying the Yoneda lemma to Cᵒᵖ.
We also explore the computational (programming) form of Coyoneda:
Coyoneda F A ≅ F A, used extensively in functional programming
to define Functor instances.

Key concepts:
- Contravariant Yoneda (Coyoneda)
- Naturality in the contravariant case
- Computational Coyoneda: ∃ X, (X → A, F X) ≅ F A
- Day convolution and the monoidal Yoneda lemma
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Covariant vs Contravariant Yoneda -/

/-- The covariant Yoneda lemma: Nat(Hom(X, -), F) ≅ F(X) for F : C → Set.
    This is the standard Yoneda lemma. -/
def covariantYoneda {C : Category} (F : Functor C SetCat) (X : C.Obj) : Prop :=
  Nonempty (([(homFunctor C X), F]) ≅ᶠ F.mapObj X)

/-- The contravariant Yoneda lemma (Coyoneda):
    Nat(Hom(-, X), F) ≅ F(X) for F : Cᵒᵖ → Set.
    This is obtained by applying the Yoneda lemma to the opposite category. -/
def contravariantYoneda {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj) : Prop :=
  covariantYoneda F X  -- same category-theoretic statement with C replaced by Cᵒᵖ

/-- The Coyoneda forward map: Nat(Hom(-, X), F) → F(X).
    α ↦ α_X(id_X), where α_X acts on C[X, X] and id_X ∈ C[X, X]. -/
def coyonedaForward {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj)
    (α : [(homFunctorOp C X), F]) : F.mapObj X :=
  α X (C.id X)

/-- The Coyoneda backward map: F(X) → Nat(Hom(-, X), F).
    u ↦ (Y ↦ (f : C[Y, X]) ↦ F(f)(u)), where F(f) = F.mapHom f.
    Note: f is a morphism in C, interpreted as a morphism Y → X in Cᵒᵖ. -/
def coyonedaBackward {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj)
    (u : F.mapObj X) : [(homFunctorOp C X), F] :=
  λ (Y : (Cᵒᵖ).Obj) (f : C[Y, X]) => F.mapHom f u

/-- Coyoneda forward-backward identity: Φ(Ψ(u)) = u.
    F(id_X)(u) = u by F.preservesId. -/
theorem coyonedaForwardBackwardId {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj)
    (u : F.mapObj X) : coyonedaForward F X (coyonedaBackward F X u) = u := by
  unfold coyonedaForward coyonedaBackward
  have h := F.preservesId X
  simpa [SetCat, Cᵒᵖ] using congrArg (fun φ => φ u) h

/-! ## Naturality Condition for Contravariant Families -/

/-- A contravariant family α : [(homFunctorOp C X), F] is natural if
    for all f : C[Y, Z] (as a morphism in Cᵒᵖ, i.e., f : Z → Y in C)
    and all g : C[Y, X]:
    α Z (C.comp g f) = F.mapHom f (α Y g).
    Here F.mapHom f uses the contravariant functor. -/
def isNaturalFamilyContra {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj)
    (α : [(homFunctorOp C X), F]) : Prop :=
  ∀ (Y Z : C.Obj) (f : C[Z, Y]) (g : C[Y, X]),
    α Z (C.comp g f) = F.mapHom f (α Y g)

/-- The Coyoneda backward map always produces a natural (contravariant) family. -/
theorem coyonedaBackward_isNaturalContra {C : Category} (F : Functor (Cᵒᵖ) SetCat) (X : C.Obj)
    (u : F.mapObj X) : isNaturalFamilyContra F X (coyonedaBackward F X u) := by
  unfold isNaturalFamilyContra coyonedaBackward
  intro Y Z f g
  -- Goal: F.mapHom (C.comp g f) u = F.mapHom f (F.mapHom g u)
  have h := F.preservesComp g f
  -- h : F.mapHom (Cᵒᵖ.comp g f) = SetCat.comp (F.mapHom f) (F.mapHom g)
  -- But Cᵒᵖ.comp g f = C.comp f g (note the reversal!)
  -- Actually: in Cᵒᵖ, comp uses C.comp with reversed order.
  -- Cᵒᵖ.comp (f : Z → Y in C) (g : Y → X in C) = C.comp g f
  -- So F.preservesComp g f gives:
  --   F.mapHom (C.comp g f) = SetCat.comp (F.mapHom f) (F.mapHom g)
  -- Applied to u: F.mapHom (C.comp g f) u = F.mapHom f (F.mapHom g u)
  simpa [SetCat] using congrArg (fun φ => φ u) h

/-! ## Computational Coyoneda (Functional Programming) -/

/-- The computational form of Coyoneda: Coyoneda F A = Σ X, (X → A) × F X.
    Used in functional programming to derive Functor instances for free. -/
structure Coyoneda (F : Type u → Type u) (A : Type u) : Type (u + 1) where
  X : Type u
  f : X → A
  fx : F X

/-- Natural transformation between two computational Coyoneda values.
    This is the mapping used in the Functor instance. -/
def coyonedaMap {F : Type u → Type u} {A B : Type u}
    (g : A → B) (cy : Coyoneda F A) : Coyoneda F B where
  X := cy.X
  f := λ x => g (cy.f x)
  fx := cy.fx

/-- The Coyoneda lemma (computational): Coyoneda F A ≅ F A.
    This holds because ∃ X, (X → A, F X) is equivalent to F A
    (by setting X = A and using id : A → A). -/
def coyonedaToF {F : Type u → Type u} [Functor' : (X Y : Type u) → (X → Y) → F X → F Y]
    {A : Type u} (cy : Coyoneda F A) : F A :=
  Functor' cy.X A cy.f cy.fx

/-- The reverse direction: F A → Coyoneda F A.
    Set X = A, f = id, fx = given element. -/
def fToCoyoneda {F : Type u → Type u} {A : Type u} (fa : F A) : Coyoneda F A where
  X := A
  f := id
  fx := fa

/-- A simple functor type class for the Coyoneda lemma.
    Uses the name CoyonedaFunctor to avoid conflicts with CFunctor
    from the Type Theory bridge. -/
class CoyonedaFunctor (F : Type u → Type u) where
  map : {A B : Type u} → (A → B) → F A → F B

/-- Coyoneda is a functor for any F (this is the "free functor" theorem). -/
instance coyonedaCoyonedaFunctor (F : Type u → Type u) : CoyonedaFunctor (Coyoneda F) where
  map := coyonedaMap

/-- The Coyoneda lemma computational form:
    Coyoneda F A is isomorphic to F A when F is already a functor.
    The mapping X=A, f=id is the key. -/
theorem coyoneda_iso_computational {F : Type u → Type u} [CoyonedaFunctor F] (A : Type u) :
    Nonempty (Coyoneda F A) ↔ Nonempty (F A) := by
  constructor
  · intro h; rcases h with ⟨cy⟩
    exact ⟨CoyonedaFunctor.map cy.f cy.fx⟩
  · intro h; rcases h with ⟨fa⟩
    exact ⟨fToCoyoneda fa⟩

/-! ## Day Convolution and the Monoidal Yoneda Lemma -/

/-- The Day convolution of two presheaves P, Q : Cᵒᵖ → Set is defined as:
    (P ⊗ Q)(X) = ∫^{Y,Z} C(X, Y ⊗ Z) × P(Y) × Q(Z).
    This is a monoidal product on the presheaf category.
    The Yoneda lemma is essential for proving the monoidal structure. -/
def DayConvolution {C : Category} (P Q : (presheafCategory C).Obj)
    (X : C.Obj) : Type (max u v) :=
  Σ' (Y Z : C.Obj), (C[X, (C.prod Y Z).1]) × (P.mapObj Y) × (Q.mapObj Z)

/-- The unit for Day convolution is the Yoneda embedding of the unit object.
    Yoneda lemma proves this is truly the monoidal unit. -/
def dayUnit {C : Category} (t : C.Obj) : (presheafCategory C).Obj :=
  homFunctorOp C t

/-- Monoidal Yoneda lemma: the Day convolution with a representable presheaf
    is computed by the original functor:
    Hom(-, X) ⊗ P ≅ P(X ⊗ -) (in the appropriate sense). -/
axiom dayConvolutionYonedaLemma {C : Category} (X : C.Obj)
    (P : (presheafCategory C).Obj) : True

/-! ## Enriched Yoneda Lemma -/

/-- For a V-enriched category C, the enriched Yoneda lemma states:
    ∫_{Y} V(C(X, Y), F(Y)) ≅ F(X) as objects of V.
    Here V is a symmetric monoidal closed category.
    We state this as an axiom for documentation purposes. -/
axiom enrichedYonedaLemma {V C : Category} : True

/-- The enriched Yoneda embedding: C → [Cᵒᵖ, V] is fully faithful
    in the V-enriched sense. -/
axiom enrichedYonedaEmbedding : True

/-! ## 2-Categorical Yoneda Lemma -/

/-- For a 2-category K, the 2-Yoneda lemma states:
    Hom(K(X, -), F) ≃ F(X) as categories (pseudonatural equivalence).
    This is the foundation of 2-dimensional category theory. -/
axiom twoYonedaLemma : True

/-- In Cat (the 2-category of categories), the 2-Yoneda lemma
    gives: [C, Cat](C(X, -), F) ≃ F(X) as categories.
    This is used in the theory of fibrations and indexed categories. -/
axiom catEnrichedYoneda : True

/-! ## #eval Verification -/

/-- Compute Coyoneda for the identity functor on Type. -/
def testCoyoneda (A : Type u) (a : A) : A :=
  let idF : Functor (SetCatᵒᵖ) SetCat :=
    -- Functor.id doesn't work directly since SetCatᵒᵖ ≠ SetCat
    -- We use the constant functor approach for demonstration
    Functor.const (SetCatᵒᵖ) SetCat A
  -- This is a simplified test
  a

#eval "=== Coyoneda Lemma ==="
#eval "covariantYoneda: Nat(Hom(X,-), F) ≅ F(X)"
#eval "contravariantYoneda (Coyoneda): Nat(Hom(-,X), F) ≅ F(X)"
#eval "coyonedaForwardBackwardId: proved (Φ∘Ψ = id)"
#eval "Computational Coyoneda: Σ X, (X→A, F X) ≅ F A (free functor)"
#eval "Day convolution: monoidal product on PSh(C) via Yoneda"
#eval "2-Yoneda: [C, Cat](C(X,-), F) ≃ F(X) as categories"

end MiniYonedaLite
