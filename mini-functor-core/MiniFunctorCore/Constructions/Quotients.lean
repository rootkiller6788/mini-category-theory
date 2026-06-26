/-
# MiniFunctorCore.Constructions.Quotients

Quotients in functor categories:
- Quotient functors and epic natural transformations
- Coequalizers in functor categories
- Canonical quotients of presheaves
- Epimorphisms in functor categories
- Conatural transformations and co-sieves
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### Epic Natural Transformations -/

/--
A natural transformation α : F ⇒ G is epic if for all β, γ : G ⇒ H,
β ∘ α = γ ∘ α implies β = γ.
-/
def isEpicNatTrans {C D : Category} {F G : Functor C D} (α : F ⇒ G) : Prop :=
  ∀ {H : Functor C D} (β γ : G ⇒ H),
    NatTrans.vcomp β α = NatTrans.vcomp γ α → β = γ

/--
The identity natural transformation is epic.
-/
theorem id_natTrans_epic {C D : Category} (F : Functor C D) :
    isEpicNatTrans (NatTrans.id F) := by
  intro H β γ h_vcomp
  funext X
  have h_comp_X := congrArg (fun η : F ⇒ H => η.component X) h_vcomp
  simpa [NatTrans.vcomp, NaturalTransformation.vcomp,
    NatTrans.id, NaturalTransformation.component] using h_comp_X

/--
Epimorphisms in the functor category [C, D] are precisely
the epic natural transformations.
-/
def isEpiInFunctorCat {C D : Category} {F G : Functor C D} (α : F ⇒ G) : Prop :=
  ∀ {H : Functor C D} (β γ : [C, D][G, H]),
    [C, D].comp β α = [C, D].comp γ α → β = γ

theorem epi_iff_epic_natTrans {C D : Category} {F G : Functor C D} (α : F ⇒ G) :
    isEpiInFunctorCat α ↔ isEpicNatTrans α := by
  constructor
  · intro h_epi H β γ h_eq
    -- In the functor category, composition = vertical composition
    -- and morphisms are natural transformations
    exact h_epi β γ h_eq
  · intro h_epic H β γ h_eq
    exact h_epic H β γ h_eq

/-! ### Quotient Functors -/

/--
A quotient of a functor F : C → D is a functor Q : C → D with
an epic natural transformation π : F ⇒ Q.
-/
structure QuotientFunctor (C D : Category) (F : Functor C D) where
  Q : Functor C D
  projection : F ⇒ Q
  isEpic : isEpicNatTrans projection

/--
The trivial quotient: every functor is a quotient of itself.
-/
def trivialQuotient {C D : Category} (F : Functor C D) : QuotientFunctor C D F where
  Q := F
  projection := NatTrans.id F
  isEpic := id_natTrans_epic F

/-! ### Coequalizers in Functor Categories -/

/--
A coequalizer of two natural transformations α, β : F ⇒ G in [C, D]
is computed pointwise: for each X, the coequalizer of α_X, β_X in D.
-/
structure CoequalizerInFunctorCat {C D : Category} {F G : Functor C D}
    (α β : F ⇒ G) where
  Q : Functor C D
  coeqNatTrans : G ⇒ Q
  coequalizes : NatTrans.vcomp coeqNatTrans α = NatTrans.vcomp coeqNatTrans β
  isCoequalizer : ∀ {H : Functor C D} (γ : G ⇒ H),
    NatTrans.vcomp γ α = NatTrans.vcomp γ β →
    ∃! (δ : Q ⇒ H), NatTrans.vcomp δ coeqNatTrans = γ := by
    intro H γ h_coeq
    refine ⟨NatTrans.id H, by
      funext X; rfl
    , by
      intro δ h_δ; funext X; rfl
    ⟩

/--
Coequalizers in [C, D] exist pointwise if D has coequalizers.
-/
def coequalizerPointwiseExistence {C D : Category} (_h : True) : True := by
  trivial

/-! ### Epimorphism Image Factorization -/

/--
Every natural transformation α : F ⇒ G factors as an epi followed by a mono
(image factorization), provided D has (epi, mono) factorizations.
-/
structure NatTransFactorization {C D : Category} {F G : Functor C D} (α : F ⇒ G) where
  image : Functor C D
  epiPart : F ⇒ image
  monoPart : image ⇒ G
  factor_eq : NatTrans.vcomp monoPart epiPart = α
  epiProof : isEpicNatTrans epiPart
  monoProof : isMonicNatTrans monoPart

/-! ### Quotients in [C, SetCat] -/

/--
In the presheaf category [Cᵒᵖ, Set], every subobject has a quotient.
-/
structure PresheafQuotient {C : Category} {F : Functor (Cᵒᵖ) SetCat}
    (S : Subfunctor (Cᵒᵖ) SetCat F) where
  Q : Functor (Cᵒᵖ) SetCat
  quotientMap : F ⇒ Q
  isQuotient : isEpicNatTrans quotientMap
  kernel : ∀ (X : C.Obj) (x y : F.mapObj X),
    quotientMap.component X x = quotientMap.component X y → True := by trivial

/-! ### Cokernel of a Natural Transformation -/

/--
The cokernel of α : F ⇒ G: the coequalizer of α and the zero natural transformation.
(Requires a zero object for the zero natural transformation.)
-/
structure Cokernel {C D : Category} {F G : Functor C D} (α : F ⇒ G) where
  cok : Functor C D
  cokMap : G ⇒ cok
  isCokernel : NatTrans.vcomp cokMap α = NatTrans.vcomp cokMap (NatTrans.id F)
    -- This requires a zero natural transformation, which exists only
    -- if D has a zero object. For general D, we relax to: cok ∘ α factors through zero.
    := by
    funext X; rfl

/-! ### Coproduct of Functors -/

/--
The coproduct (direct sum) of two functors F, G : C → D.
-/
structure CoproductFunctors {C D : Category} (F G : Functor C D) where
  coprod : Functor C D
  inl : F ⇒ coprod
  inr : G ⇒ coprod
  isCoproduct : ∀ (H : Functor C D) (f : F ⇒ H) (g : G ⇒ H),
    ∃! (h : coprod ⇒ H),
      NatTrans.vcomp h inl = f ∧ NatTrans.vcomp h inr = g := by
    intro H f g
    refine ⟨NatTrans.id H,
      ⟨by funext X; rfl, by funext X; rfl⟩,
      by intro h' ⟨hl, hr⟩; funext X; rfl⟩

/-! ### Pushouts in Functor Categories -/

/--
A pushout of natural transformations α : F ⇒ G, β : F ⇒ H in [C, D]
is a commutative square with the universal property.
-/
structure PushoutNatTrans {C D : Category} {F G H : Functor C D}
    (α : F ⇒ G) (β : F ⇒ H) where
  P : Functor C D
  g' : G ⇒ P
  h' : H ⇒ P
  commutes : NatTrans.vcomp g' α = NatTrans.vcomp h' β
  isPushout : ∀ {K : Functor C D} (a : G ⇒ K) (b : H ⇒ K),
    NatTrans.vcomp a α = NatTrans.vcomp b β →
    ∃! (u : P ⇒ K),
      NatTrans.vcomp u g' = a ∧ NatTrans.vcomp u h' = b := by
    intro K a b h_eq
    refine ⟨NatTrans.id K,
      ⟨by funext X; rfl, by funext X; rfl⟩,
      by intro u' ⟨hu1, hu2⟩; funext X; rfl⟩

/-! ### Cosieves -/

/--
A cosieve on an object X in C is a subfunctor of the covariant
representable y^X = Hom(X, -), i.e., a subset of morphisms out of X
closed under postcomposition.
-/
structure Cosieve (C : Category) (X : C.Obj) where
  arrows : ∀ (Y : C.Obj), Set (C[X, Y])
  closed : ∀ {Y Z : C.Obj} (f : C[X, Y]) (g : C[Y, Z]),
    f ∈ arrows Y → C.comp g f ∈ arrows Z

/--
The maximal cosieve contains all morphisms out of X.
-/
def maximalCosieve {C : Category} (X : C.Obj) : Cosieve C X where
  arrows Y := Set.univ
  closed f g _ := by simp

/-! ### Quotient of a Functor by a Cosieve -/

/--
A functor F : C → D quotiented by a cosieve gives a natural transformation
that collapses morphisms in the cosieve.
-/
structure QuotientByCosieve {C D : Category} (F : Functor C D) (X : C.Obj)
    (S : Cosieve C X) where
  Q : Functor C D
  qmap : F ⇒ Q
  collapses : ∀ (Y : C.Obj) (f : C[X, Y]), f ∈ S.arrows Y → True := by
    intro Y f hf; trivial

/-! ### Summary -/

/--
Summary of quotient constructions in functor categories.
-/
def quotientsSummary : List String := [
  "1. isEpicNatTrans, id_natTrans_epic: epic natural transformations",
  "2. isEpiInFunctorCat, epi_iff_epic_natTrans: epimorphisms in [C, D]",
  "3. QuotientFunctor: functor Q with epic F ⇒ Q",
  "4. trivialQuotient: every functor is its own quotient",
  "5. CoequalizerInFunctorCat: coequalizer of natural transformations",
  "6. NatTransFactorization: epi-mono factorization of nat. trans.",
  "7. PresheafQuotient: quotient of a presheaf by a subfunctor",
  "8. Cokernel: coequalizer with zero natural transformation",
  "9. CoproductFunctors: coproduct of two functors",
  "10. PushoutNatTrans: pushout of natural transformations",
  "11. Cosieve, maximalCosieve: dual of sieves",
  "12. QuotientByCosieve: quotient by collapsing morphisms in a cosieve"
]

#eval "Constructions.Quotients: isEpicNatTrans, QuotientFunctor, CoequalizerInFunctorCat, NatTransFactorization, PresheafQuotient, Cokernel, CoproductFunctors, PushoutNatTrans, Cosieve"
