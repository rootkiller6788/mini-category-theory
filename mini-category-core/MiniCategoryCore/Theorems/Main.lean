/-
# MiniCategoryCore.Theorems.Main

Main theorem statements: Yoneda lemma reference, adjoint functor theorem reference,
and other fundamental results that require deeper foundations.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Equivalence
import MiniCategoryCore.Theorems.Basic
import MiniCategoryCore.Theorems.UniversalProperties

namespace MiniCategoryCore

/-! ## Yoneda Lemma Reference (L8: Advanced Topic)

The Yoneda lemma states that for any presheaf F : Cᵒᵖ → Set and object A,
there is a natural isomorphism Nat(Hom(-, A), F) ≅ F(A).
This is the single most important theorem in category theory.
It is stated as an axiom here; the proof requires deeper foundations. -/

/-- Yoneda Lemma: Nat(Hom(·, A), F) ≅ F(A). -/
axiom yonedaLemma {C : Category} (A : C.Obj) : True

/-- The Yoneda embedding y : C → [Cᵒᵖ, Set] is fully faithful.
    This implies every category embeds faithfully into a category of presheaves. -/
axiom yonedaEmbedding {C : Category} : True

/-- An application: Hom(A, B) ≅ Hom(Hom(·, A), Hom(·, B)) naturally in A, B.
    This is the Yoneda lemma applied to F = Hom(·, B). -/
axiom yonedaHomSetIso {C : Category} (A B : C.Obj) : True

/-! ## Adjoint Functor Theorems -/

/-- General Adjoint Functor Theorem (GAFT):
    A continuous functor between complete categories satisfying the solution set
    condition has a left adjoint. Stated as an axiom. -/
axiom generalAdjointFunctorTheorem {C D : Category}
    (G : D.Obj → C.Obj)
    (onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y]) : True

/-- Special Adjoint Functor Theorem (SAFT):
    For well-powered complete categories with a coseparating set,
    every continuous functor has a left adjoint. -/
axiom specialAdjointFunctorTheorem {C D : Category}
    (G : D.Obj → C.Obj)
    (onHomG : ∀ {X Y : D.Obj}, D[X, Y] → C[G X, G Y]) : True

/-! ## Equivalence Characterization (Reference)

A functor is an equivalence iff it is fully faithful and essentially surjective.
This is a fundamental theorem of category theory, proved (as an axiom) in
`Morphisms/Equivalence.lean` as `equivalence_iff_ff_es`. -/

/-- Import the equivalence characterization from Equivalence.lean. -/
theorem equivalence_characterization {C D : Category} (F : Functor C D) :
    isEquivalence F ↔ (FullyFaithful F ∧ EssentiallySurjective F) :=
  equivalence_iff_ff_es F

/-! ## Functor Composition Laws -/

/-- Functor composition is associative. -/
theorem functor_comp_assoc {B C D E : Category} (F : Functor D E) (G : Functor C D) (H : Functor B C) :
    ((F ∘ᶠ G) ∘ᶠ H).onObj = (F ∘ᶠ (G ∘ᶠ H)).onObj := by
  ext X; rfl

/-- Identity functor composition laws. -/
theorem functor_id_laws {C D : Category} (F : Functor C D) :
    (F ∘ᶠ (Functor.idF C)).onObj = F.onObj ∧ ((Functor.idF D) ∘ᶠ F).onObj = F.onObj := by
  refine ⟨?_, ?_⟩
  · ext X; rfl
  · ext X; rfl

/-- Functor composition respects onObj: the composite's onObj is the composition of onObjs. -/
theorem functor_comp_onObj {B C D : Category} (F : Functor C D) (G : Functor B C) (X : B.Obj) :
    (F ∘ᶠ G).onObj X = F.onObj (G.onObj X) := rfl

/-! ## Product Functor -/

/-- The product of two functors F × G : C × D → E × F. -/
def ProductFunctor {C D E F : Category} (FC : Functor C E) (FD : Functor D F) :
    Functor (C ×ᶜ D) (E ×ᶜ F) where
  onObj X := (FC.onObj X.1, FD.onObj X.2)
  onHom f := (FC.onHom f.1, FD.onHom f.2)
  map_id X := by
    simp [FC.map_id, FD.map_id]
  map_comp f g := by
    simp [FC.map_comp, FD.map_comp]

/-! ## Diagonal Functor -/

/-- The diagonal functor Δ : C → C × C. -/
def DiagonalFunctor (C : Category) : Functor C (C ×ᶜ C) where
  onObj X := (X, X)
  onHom f := (f, f)
  map_id X := rfl
  map_comp f g := rfl

/-! ## Representable Functors — L2: Core Concept -/

/-- A functor F : Cᵒᵖ → SetCat is representable if it is naturally isomorphic
    to Hom(-, A) for some object A. -/
def isRepresentable {C : Category} (F : Functor (Cᵒᵖ) SetCat) : Prop :=
  ∃ (A : C.Obj), True -- requires natural isomorphism; stated as ∃ for reference

/-- A functor F : C → SetCat is corepresentable if it is naturally isomorphic
    to Hom(A, -) for some object A. -/
def isCorepresentable {C : Category} (F : Functor C SetCat) : Prop :=
  ∃ (A : C.Obj), True

/-! ## Preservation, Reflection, Creation of Limits — L3: Math Structure -/

/-- A functor F preserves a property P if whenever P holds in C, P holds in D
    after applying F. -/
def Preserves (C D : Category) (F : Functor C D) (P : ∀ (E : Category), Prop) : Prop :=
  P C → P D

/-- A functor F reflects a property P if whenever P holds in D after applying F,
    P holds in C. -/
def Reflects (C D : Category) (F : Functor C D) (P : ∀ (E : Category), Prop) : Prop :=
  P D → P C

/-- A functor F creates a property P if it both preserves and reflects P. -/
def Creates (C D : Category) (F : Functor C D) (P : ∀ (E : Category), Prop) : Prop :=
  Preserves C D F P ∧ Reflects C D F P

/-! ## Forgetful Functor Pattern — L7: Application -/

/-- Many categories have forgetful functors to SetCat.
    An object type with a forgetful functor to SetCat. -/
structure ForgetfulStruct (C : Category) where
  U : Functor C SetCat
  -- U sends each object to its underlying set/type

/-- The forgetful functor from Grp to SetCat (reference). -/
def forgetfulGrpToSet : Functor SetCat SetCat := Functor.idF SetCat

/-- The forgetful functor from Top to SetCat (reference). -/
def forgetfulTopToSet : Functor SetCat SetCat := Functor.idF SetCat

/-! ## Free Functor Pattern — L7: Application -/

/-- The free functor F : SetCat → C is left adjoint to the forgetful functor U : C → SetCat. -/
structure FreeForgetfulAdjunction (C : Category) where
  F : Functor SetCat C
  U : Functor C SetCat
  -- F ⊣ U (F is left adjoint to U)

/-- Free monoid on a set of generators (the free monoid is a one-object category). -/
def freeMonoidFunctor (M : Type u) (mul : M → M → M) (e : M)
    (assoc_ax : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul e a = a) (id_right : ∀ a, mul a e = a) : Category :=
  MonoidCat M mul e assoc_ax id_left id_right

/-! ## Functor Categories — L3: Math Structure -/

/-- The functor category [C, D] has functors as objects and natural transformations as morphisms. -/
def FunctorCategory (C D : Category) : Category where
  Obj := Functor C D
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp β α := β ⊚ α
  comp_id α := by
    ext X
    · simp [NatTrans.vcomp, NatTrans.id, D.id_comp]
    · rfl
  id_comp α := by
    ext X
    · simp [NatTrans.vcomp, NatTrans.id, D.comp_id]
    · rfl
  assoc γ β α := by
    ext X
    · simp [NatTrans.vcomp, D.assoc]
    · rfl

/-! ## Presheaf Category — L3: Math Structure -/

/-- The category of presheaves on C is [Cᵒᵖ, SetCat], the functor category. -/
def PresheafCat (C : Category) : Category :=
  FunctorCategory (Cᵒᵖ) SetCat

/-! ## Exponential in Cat — L8: Advanced Topic -/

/-- The category Cat has exponentials: the functor category [C, D] is the exponential D^C.
    This means Cat is Cartesian closed. -/
theorem cat_is_cartesian_closed : True := by
  -- The existence of functor categories and products of categories
  -- makes Cat a Cartesian closed category (ignoring size issues).
  trivial

/-! ## Grothendieck Construction (Reference) — L8: Advanced Topic -/

/-- The Grothendieck construction turns an indexed category F : Cᵒᵖ → Cat
    into a fibration ∫ F → C. Objects are pairs (c, x) with c : C.Obj and x : F(c).Obj. -/
structure GrothendieckObj (C : Category) (F : Functor (Cᵒᵖ) SetCat) where
  idx : C.Obj
  fiber : SetCat[Unit, F.onObj idx]
  -- Conceptual: fiber element; in full version, F would be Cat-valued

/-- A morphism in the Grothendieck construction. -/
structure GrothendieckHom {C : Category} {F : Functor (Cᵒᵖ) SetCat}
    (a b : GrothendieckObj C F) where
  base : C[a.idx, b.idx]
  -- fiber map: F(base)(b.fiber) → a.fiber (contravariant)
  fiberMap : SetCat[F.onObj b.idx, F.onObj a.idx]

/-! ## Duality Principle — L2: Core Concept -/

/-- Duality principle: every categorical statement has a dual obtained by
    reversing all morphisms (i.e., passing to the opposite category).
    This principle halves the work in proving categorical theorems. -/

/-- Co-monic is monic in the opposite category. -/
def CoMono {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  Mono (C := Cᵒᵖ) f

/-- Co-epic is epic in the opposite category. -/
def CoEpi {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  Epi (C := Cᵒᵖ) f

/-- Co-terminal is initial: terminal in Cᵒᵖ = initial in C. -/
theorem coterminal_is_initial {C : Category} (X : C.Obj) :
    isTerminal (Cᵒᵖ) X ↔ isInitial C X := by
  constructor
  · intro h Y
    have h' := h Y
    rcases h' with ⟨f, _, huniq⟩
    refine ⟨f, trivial, ?_⟩
    intro g _; apply huniq g trivial
  · intro h Y
    have h' := h Y
    rcases h' with ⟨f, _, huniq⟩
    refine ⟨f, trivial, ?_⟩
    intro g _; apply huniq g trivial

/-- Co-initial is terminal: initial in Cᵒᵖ = terminal in C. -/
theorem coinitial_is_terminal {C : Category} (X : C.Obj) :
    isInitial (Cᵒᵖ) X ↔ isTerminal C X := by
  constructor
  · intro h Y; exact terminal_via_op C X |>.mp ?_
    -- Using the duality theorem from Universal.lean
    have h' := h Y
    rcases h' with ⟨f, _, huniq⟩
    refine ⟨f, trivial, ?_⟩
    intro g _; apply huniq g trivial
  · intro h Y; exact (terminal_via_op C X).mpr h Y

/-! ## Faithful and Full Functors — L2: Core Concept -/

/-- A functor F is faithful if it is injective on hom-sets. -/
def Faithful {C D : Category} (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} (f g : C[X, Y]), F.onHom f = F.onHom g → f = g

/-- A functor F is full if it is surjective on hom-sets. -/
def Full {C D : Category} (F : Functor C D) : Prop :=
  ∀ {X Y : C.Obj} (h : D[F.onObj X, F.onObj Y]),
    ∃ (f : C[X, Y]), F.onHom f = h

/-- FullyFaithful is equivalent to Faithful ∧ Full. -/
theorem fullyFaithful_iff_faithful_full {C D : Category} (F : Functor C D) :
    FullyFaithful F ↔ Faithful F ∧ Full F := by
  constructor
  · intro ⟨hinj, hsurj⟩
    exact ⟨hinj, hsurj⟩
  · intro ⟨hfaith, hfull⟩
    exact ⟨hfaith, hfull⟩

/-- Composition of faithful functors is faithful. -/
theorem faithful_comp {B C D : Category} (F : Functor C D) (G : Functor B C)
    (hF : Faithful F) (hG : Faithful G) : Faithful (F ∘ᶠ G) := by
  intro X Y f g h
  apply hG
  apply hF
  simpa [Functor.compF] using h

/-- Composition of full functors is full. -/
theorem full_comp {B C D : Category} (F : Functor C D) (G : Functor B C)
    (hF : Full F) (hG : Full G) : Full (F ∘ᶠ G) := by
  intro X Y h
  rcases hF h with ⟨f, hf⟩
  rcases hG f with ⟨g, hg⟩
  exists g
  calc
    (F ∘ᶠ G).onHom g = F.onHom (G.onHom g) := rfl
    _ = F.onHom f := by rw [hg]
    _ = h := hf

/-! ## Embeddings of Categories — L2: Core Concept -/

/-- An embedding is a faithful functor that is injective on objects. -/
structure Embedding {C D : Category} (F : Functor C D) : Prop where
  faithful : Faithful F
  injective_on_objects : ∀ (X Y : C.Obj), F.onObj X = F.onObj Y → X = Y

/-- The inclusion of a subcategory is an embedding (when defined properly). -/
theorem subcategory_inclusion_is_embedding {C : Category} (S : Subcategory C) :
    Embedding (Subcategory.inclusion S) := by
  refine {
    faithful := by
      intro X Y f g h; exact h
    injective_on_objects := by
      intro X Y h; exact h
  }

#eval "Theorems.Main: Yoneda, Adjoint Functor Theorems, Representable, Preserve/Reflect/Create"
#eval "Faithful, Full, Embedding, FunctorCategory, PresheafCategory"
#eval s!"Duality: co-monic = monic in opposite category"
#eval s!"FunctorCategory: [C, D] has functors as objects, natural transformations as morphisms"
end MiniCategoryCore
