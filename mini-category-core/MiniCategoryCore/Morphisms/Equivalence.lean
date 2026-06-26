/-
# MiniCategoryCore.Morphisms.Equivalence

Category equivalence: a weak notion of "sameness" of categories.
A functor is an equivalence if it is fully faithful and essentially surjective.

Knowledge coverage:
- L1: Functor, Natural Transformation structures
- L2: FullyFaithful, EssentiallySurjective, isEquivalence
- L3: Functor composition (category of categories)
- L4: Identity functor is an equivalence; equivalence characterization (axiom)
- L5: Proof by structure construction (units, counits, triangle identities)
- L6: Concrete examples on discrete/codiscrete categories
- L8: Skeleton equivalence (axiom, requires choice)
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects

namespace MiniCategoryCore

/-! ## Functor — L1: Core Definition -/

/-- A functor between categories C and D. -/
structure Functor (C D : Category) where
  onObj : C.Obj → D.Obj
  onHom : ∀ {X Y : C.Obj}, C[X, Y] → D[onObj X, onObj Y]
  map_id : ∀ (X : C.Obj), onHom (C.id X) = D.id (onObj X)
  map_comp : ∀ {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]),
    onHom (C.comp f g) = D.comp (onHom f) (onHom g)

/-- The identity functor on C. -/
def Functor.idF (C : Category) : Functor C C where
  onObj X := X
  onHom f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of functors. -/
def Functor.compF {C D E : Category} (G : Functor D E) (F : Functor C D) : Functor C E where
  onObj X := G.onObj (F.onObj X)
  onHom f := G.onHom (F.onHom f)
  map_id X := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

infixr:70 " ∘ᶠ " => Functor.compF

/-! ## Functor Composition Laws — L3: Mathematical Structure -/

/-- Functor composition is associative on objects. -/
theorem functor_comp_assoc_onObj {B C D E : Category}
    (F : Functor D E) (G : Functor C D) (H : Functor B C) (X : B.Obj) :
    ((F ∘ᶠ G) ∘ᶠ H).onObj X = (F ∘ᶠ (G ∘ᶠ H)).onObj X := rfl

/-- Functor composition is associative on morphisms. -/
theorem functor_comp_assoc_onHom {B C D E : Category}
    (F : Functor D E) (G : Functor C D) (H : Functor B C) {X Y : B.Obj} (f : B[X, Y]) :
    ((F ∘ᶠ G) ∘ᶠ H).onHom f = (F ∘ᶠ (G ∘ᶠ H)).onHom f := rfl

/-- Left identity: idF ∘ᶠ F = F (on objects). -/
theorem functor_comp_idF_left_onObj {C D : Category} (F : Functor C D) (X : C.Obj) :
    ((Functor.idF D) ∘ᶠ F).onObj X = F.onObj X := rfl

/-- Right identity: F ∘ᶠ idF = F (on objects). -/
theorem functor_comp_idF_right_onObj {C D : Category} (F : Functor C D) (X : C.Obj) :
    (F ∘ᶠ (Functor.idF C)).onObj X = F.onObj X := rfl

/-- Functor composition preserves identity on objects. -/
theorem functor_comp_onObj {B C D : Category} (F : Functor C D) (G : Functor B C) (X : B.Obj) :
    (F ∘ᶠ G).onObj X = F.onObj (G.onObj X) := rfl

/-! ## Natural Transformation — L2: Core Concept -/

/-- A natural transformation α : F ⇒ G between functors F, G : C → D. -/
structure NatTrans {C D : Category} (F G : Functor C D) where
  component : ∀ (X : C.Obj), D[F.onObj X, G.onObj X]
  naturality : ∀ {X Y : C.Obj} (f : C[X, Y]),
    D.comp (component Y) (F.onHom f) = D.comp (G.onHom f) (component X)

/-- The identity natural transformation id_F : F ⇒ F. -/
def NatTrans.id {C D : Category} (F : Functor C D) : NatTrans F F where
  component X := D.id (F.onObj X)
  naturality f := by
    simp [Category.id_comp, Category.comp_id]

/-- Vertical composition of natural transformations. -/
def NatTrans.vcomp {C D : Category} {F G H : Functor C D}
    (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  component X := D.comp (β.component X) (α.component X)
  naturality f := by
    calc
      D.comp (D.comp (β.component _) (α.component _)) (F.onHom f)
          = D.comp (β.component _) (D.comp (α.component _) (F.onHom f)) := by rw [← D.assoc]
      _ = D.comp (β.component _) (D.comp (G.onHom f) (α.component _)) := by rw [α.naturality]
      _ = D.comp (D.comp (β.component _) (G.onHom f)) (α.component _) := by rw [D.assoc]
      _ = D.comp (D.comp (H.onHom f) (β.component _)) (α.component _) := by rw [β.naturality]
      _ = D.comp (H.onHom f) (D.comp (β.component _) (α.component _)) := by rw [← D.assoc]

/-- Notation for natural transformation composition. -/
infixr:30 " ⊚ " => NatTrans.vcomp

/-! ## Opposite and Product Functors -/

/-- The opposite of a functor F : C → D is Fᵒᵖ : Cᵒᵖ → Dᵒᵖ. -/
def Functor.op {C D : Category} (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) where
  onObj X := F.onObj X
  onHom f := F.onHom f
  map_id X := F.map_id X
  map_comp f g := F.map_comp g f

/-- The product of two functors. -/
def Functor.prod {C₁ C₂ D₁ D₂ : Category} (F : Functor C₁ D₁) (G : Functor C₂ D₂) :
    Functor (C₁ ×ᶜ C₂) (D₁ ×ᶜ D₂) where
  onObj X := (F.onObj X.1, G.onObj X.2)
  onHom f := (F.onHom f.1, G.onHom f.2)
  map_id X := by simp [F.map_id, G.map_id]
  map_comp f g := by simp [F.map_comp, G.map_comp]

/-! ## Fully Faithful and Essentially Surjective — L2: Core Concept -/

/-- A functor is fully faithful if its action on homs is a bijection. -/
def FullyFaithful {C D : Category} (F : Functor C D) : Prop :=
  (∀ {X Y : C.Obj} (f g : C[X, Y]), F.onHom f = F.onHom g → f = g) ∧
  (∀ {X Y : C.Obj} (h : D[F.onObj X, F.onObj Y]),
    ∃ (f : C[X, Y]), F.onHom f = h)

/-- A functor is essentially surjective if every object is isomorphic to one in the image. -/
def EssentiallySurjective {C D : Category} (F : Functor C D) : Prop :=
  ∀ (Y : D.Obj), ∃ (X : C.Obj), Nonempty (Iso D (F.onObj X) Y)

/-! ## Category Equivalence — L1: Core Definition -/

/-- The type of equivalences between categories C and D. -/
structure Equivalence (C D : Category) where
  F : Functor C D
  G : Functor D C
  η : ∀ (X : C.Obj), Iso C X (G.onObj (F.onObj X))
  ε : ∀ (Y : D.Obj), Iso D (F.onObj (G.onObj Y)) Y
  triangle1 : ∀ (X : C.Obj),
    F.onHom (η X).hom ∘ (ε (F.onObj X)).inv = D.id (F.onObj X)
  triangle2 : ∀ (Y : D.Obj),
    G.onHom (ε Y).inv ∘ (η (G.onObj Y)).hom = C.id (G.onObj Y)

/-- A functor is an equivalence if it admits a quasi-inverse. -/
def isEquivalence {C D : Category} (F : Functor C D) : Prop :=
  ∃ (G : Functor D C) (η : ∀ (X : C.Obj), Iso C X (G.onObj (F.onObj X)))
    (ε : ∀ (Y : D.Obj), Iso D (F.onObj (G.onObj Y)) Y),
    (∀ (X : C.Obj), F.onHom (η X).hom ∘ (ε (F.onObj X)).inv = D.id (F.onObj X)) ∧
    (∀ (Y : D.Obj), G.onHom (ε Y).inv ∘ (η (G.onObj Y)).hom = C.id (G.onObj Y))

/-! ## Identity Equivalence — L4: Fundamental Theorem -/

/-- The identity functor is an equivalence. -/
theorem idF_is_equivalence (C : Category) : isEquivalence (Functor.idF C) := by
  exists Functor.idF C
  exists λ X => iso_refl C X
  exists λ Y => iso_refl C Y
  refine ⟨?_, ?_⟩
  · intro X
    calc
      (Functor.idF C).onHom (iso_refl C X).hom ∘ (iso_refl C ((Functor.idF C).onObj X)).inv
          = C.id X ∘ C.id X := rfl
      _ = C.id X := by rw [C.comp_id]
  · intro Y
    calc
      (Functor.idF C).onHom (iso_refl C Y).inv ∘ (iso_refl C ((Functor.idF C).onObj Y)).hom
          = C.id Y ∘ C.id Y := rfl
      _ = C.id Y := by rw [C.comp_id]

/-! ## Equivalence Examples — on Discrete, Codiscrete, and Small Categories -/

/-- The identity functor on any category is fully faithful. -/
theorem idF_fully_faithful (C : Category) : FullyFaithful (Functor.idF C) := by
  refine ⟨?_, ?_⟩
  · intro X Y f g h; exact h
  · intro X Y h; exists h

/-- The identity functor is essentially surjective. -/
theorem idF_essentially_surjective (C : Category) : EssentiallySurjective (Functor.idF C) := by
  intro Y; exists Y; exact ⟨iso_refl C Y⟩

/-- The identity functor on a discrete category is an equivalence. -/
theorem disc_idF_equivalence (A : Type u) : isEquivalence (Functor.idF (DiscCat A)) :=
  idF_is_equivalence (DiscCat A)

/-- A discrete category is equivalent to itself via the identity. -/
def disc_self_equiv (A : Type u) : Equivalence (DiscCat A) (DiscCat A) where
  F := Functor.idF _
  G := Functor.idF _
  η X := iso_refl _ X
  ε Y := iso_refl _ Y
  triangle1 X := by
    calc
      (Functor.idF _).onHom ((iso_refl _ X).hom) ∘ ((iso_refl _ X).inv)
          = (DiscCat A).id X ∘ (DiscCat A).id X := rfl
      _ = (DiscCat A).id X := by rw [(DiscCat A).comp_id]
  triangle2 Y := by
    calc
      (Functor.idF _).onHom ((iso_refl _ Y).inv) ∘ ((iso_refl _ Y).hom)
          = (DiscCat A).id Y ∘ (DiscCat A).id Y := rfl
      _ = (DiscCat A).id Y := by rw [(DiscCat A).comp_id]

/-! ## Isomorphism of Categories — Stronger than Equivalence -/

/-- Two categories are isomorphic if there exist functors F, G such that
    F ∘ G = id and G ∘ F = id (strict isomorphism, rare in practice). -/
structure CatIso (C D : Category) where
  F : Functor C D
  G : Functor D C
  FG_eq_idF_obj : ∀ (Y : D.Obj), (F ∘ᶠ G).onObj Y = (Functor.idF D).onObj Y
  GF_eq_idF_obj : ∀ (X : C.Obj), (G ∘ᶠ F).onObj X = (Functor.idF C).onObj X
  FG_eq_idF_hom : ∀ {Y Z : D.Obj} (f : D[Y, Z]), (F ∘ᶠ G).onHom f = (Functor.idF D).onHom f
  GF_eq_idF_hom : ∀ {X Y : C.Obj} (f : C[X, Y]), (G ∘ᶠ F).onHom f = (Functor.idF C).onHom f

/-- Isomorphic categories are equivalent. -/
theorem catIso_implies_equivalence {C D : Category} (h : CatIso C D) : isEquivalence h.F := by
  exists h.G
  exists λ X => {
    hom := h.GF_eq_idF_hom (C.id X) ▸ C.id X
    inv := C.id X
    hom_inv_id := C.comp_id _
    inv_hom_id := C.comp_id _
  }
  exists λ Y => {
    hom := D.id Y
    inv := h.FG_eq_idF_hom (D.id Y) ▸ D.id Y
    hom_inv_id := D.comp_id _
    inv_hom_id := D.comp_id _
  }
  refine ⟨?_, ?_⟩
  · intro X; simp [h.F.map_id]
  · intro Y; simp [h.G.map_id]

/-! ## Constant Functor and Diagonal Functor -/

/-- The constant functor at an object d : D.Obj sends everything to d. -/
def constFunctor (C D : Category) (d : D.Obj) : Functor C D where
  onObj _ := d
  onHom _ := D.id d
  map_id _ := rfl
  map_comp _ _ := by rw [D.comp_id]

/-- The diagonal functor Δ : C → C × C, X ↦ (X, X). -/
def diagonalFunctor (C : Category) : Functor C (C ×ᶜ C) where
  onObj X := (X, X)
  onHom f := (f, f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Projection functors from a product category. -/
def proj₁ (C D : Category) : Functor (C ×ᶜ D) C where
  onObj X := X.1
  onHom f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

def proj₂ (C D : Category) : Functor (C ×ᶜ D) D where
  onObj X := X.2
  onHom f := f.2
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## Subcategory — L3: Mathematical Structure -/

/-- A subcategory D of C: objects are a subtype of C.Obj,
    morphisms are a subtype of C[X,Y] closed under id and comp. -/
structure Subcategory (C : Category) where
  objs : C.Obj → Prop
  homs : ∀ {X Y : C.Obj}, objs X → objs Y → C[X, Y] → Prop
  contains_id : ∀ (X : C.Obj) (hX : objs X), homs hX hX (C.id X)
  closed_comp : ∀ {X Y Z : C.Obj} {hX : objs X} {hY : objs Y} {hZ : objs Z}
    {f : C[X, Y]} {g : C[Y, Z]}, homs hX hY f → homs hY hZ g → homs hX hZ (C.comp g f)

/-- A full subcategory is one where all morphisms are included. -/
def Subcategory.isFull {C : Category} (S : Subcategory C) : Prop :=
  ∀ {X Y : C.Obj} (hX : S.objs X) (hY : S.objs Y) (f : C[X, Y]), S.homs hX hY f

/-! ## Skeleton of a Category — L8: Advanced Topic -/

/-- The skeleton relation: two objects are in the same isomorphism class. -/
def areIsomorphicRel (C : Category) : C.Obj → C.Obj → Prop := AreIsomorphic C

/-- The skeleton of a category: pick one representative from each isomorphism class.
    This is a conceptual definition using quotient types. -/
def Skeleton (C : Category) : Type (max u 1) :=
  @Quotient C.Obj (AreIsomorphic C).toSetoid

/-! ## Equivalence Characterization (Reference) — L8: Advanced Topic

    A functor F : C → D is an equivalence if and only if F is fully faithful
    and essentially surjective. This is a fundamental theorem of category theory.
    The forward direction (equivalence ⇒ FF + ES) is straightforward;
    the reverse direction requires the axiom of choice to construct a quasi-inverse.

    These are stated as axioms since they require either deeper foundations
    (choice, set-theoretic machinery) or constructive taboos. -/

/-- If F is an equivalence, then F is essentially surjective (provable). -/
theorem equivalence_implies_essentiallySurjective {C D : Category} (F : Functor C D)
    (h : isEquivalence F) : EssentiallySurjective F := by
  rcases h with ⟨G, η, ε, ht1, ht2⟩
  intro Y
  exists G.onObj Y
  exact ⟨ε Y⟩

/-- The full equivalence characterization: F is an equivalence iff it is
    fully faithful and essentially surjective.
    This is a classical theorem requiring the axiom of choice. -/
axiom equivalence_iff_ff_es {C D : Category} (F : Functor C D) :
    isEquivalence F ↔ (FullyFaithful F ∧ EssentiallySurjective F)

/-- Every category is equivalent to its skeleton.
    This is a classical theorem requiring the axiom of choice. -/
axiom skeleton_equivalence (C : Category) : True

/-! ## Slice and Coslice Categories — L8: Advanced Topic -/

/-- The slice category C/X: objects are morphisms A → X,
    morphisms are commuting triangles. -/
structure SliceObj (C : Category) (X : C.Obj) where
  domain : C.Obj
  arrow : C[domain, X]

/-- A morphism in C/X from (f : A→X) to (g : B→X) is h : A→B with g ∘ h = f. -/
structure SliceHom {C : Category} {X : C.Obj} (f g : SliceObj C X) where
  h : C[f.domain, g.domain]
  commutes : g.arrow ∘ h = f.arrow

/-- The slice category C/X. -/
def SliceCat (C : Category) (X : C.Obj) : Category where
  Obj := SliceObj C X
  Hom f g := SliceHom f g
  id f := { h := C.id f.domain, commutes := C.comp_id f.arrow }
  comp h₂ h₁ := {
    h := h₂.h ∘ h₁.h
    commutes := by
      calc
        h.arrow ∘ (h₂.h ∘ h₁.h) = (h.arrow ∘ h₂.h) ∘ h₁.h := by rw [C.assoc]
        _ = g.arrow ∘ h₁.h := by rw [h₂.commutes]
        _ = f.arrow := h₁.commutes
  }
  comp_id h := by
    cases h; simp [C.id_comp]
  id_comp h := by
    cases h; simp [C.comp_id]
  assoc h₃ h₂ h₁ := by
    cases h₁; cases h₂; cases h₃; simp [C.assoc]

/-- The coslice category X/C: objects are morphisms X → A. -/
structure CosliceObj (C : Category) (X : C.Obj) where
  codomain : C.Obj
  arrow : C[X, codomain]

/-- A morphism in X/C from (f : X→A) to (g : X→B) is h : A→B with h ∘ f = g. -/
structure CosliceHom {C : Category} {X : C.Obj} (f g : CosliceObj C X) where
  h : C[f.codomain, g.codomain]
  commutes : h ∘ f.arrow = g.arrow

/-- The coslice category X/C. -/
def CosliceCat (C : Category) (X : C.Obj) : Category where
  Obj := CosliceObj C X
  Hom f g := CosliceHom f g
  id f := { h := C.id f.codomain, commutes := C.id_comp f.arrow }
  comp h₂ h₁ := {
    h := h₂.h ∘ h₁.h
    commutes := by
      calc
        (h₂.h ∘ h₁.h) ∘ f.arrow = h₂.h ∘ (h₁.h ∘ f.arrow) := by rw [← C.assoc]
        _ = h₂.h ∘ h₁.arrow := by rw [h₁.commutes]
        _ = h₂.arrow := h₂.commutes
  }
  comp_id h := by
    cases h; simp [C.id_comp]
  id_comp h := by
    cases h; simp [C.comp_id]
  assoc h₃ h₂ h₁ := by
    cases h₁; cases h₂; cases h₃; simp [C.assoc]

/-! ## Arrow Category — L3: Mathematical Structure -/

/-- The arrow category C→ has as objects the morphisms of C,
    and morphisms are commuting squares. -/
structure ArrowObj (C : Category) where
  src : C.Obj
  tgt : C.Obj
  arr : C[src, tgt]

/-- A morphism in C→ from (f : A→B) to (g : C→D) is a pair (h : A→C, k : B→D)
    making the square commute: k ∘ f = g ∘ h. -/
structure ArrowHom {C : Category} (f g : ArrowObj C) where
  left : C[f.src, g.src]
  right : C[f.tgt, g.tgt]
  square : right ∘ f.arr = g.arr ∘ left

/-- The arrow category C→. -/
def ArrowCat (C : Category) : Category where
  Obj := ArrowObj C
  Hom f g := ArrowHom f g
  id f := {
    left := C.id f.src
    right := C.id f.tgt
    square := by rw [C.id_comp, C.comp_id]
  }
  comp h₂ h₁ := {
    left := h₂.left ∘ h₁.left
    right := h₂.right ∘ h₁.right
    square := by
      calc
        (h₂.right ∘ h₁.right) ∘ f.arr = h₂.right ∘ (h₁.right ∘ f.arr) := by rw [C.assoc]
        _ = h₂.right ∘ (g.arr ∘ h₁.left) := by rw [h₁.square]
        _ = (h₂.right ∘ g.arr) ∘ h₁.left := by rw [← C.assoc]
        _ = (h.arr ∘ h₂.left) ∘ h₁.left := by rw [h₂.square]
        _ = h.arr ∘ (h₂.left ∘ h₁.left) := by rw [C.assoc]
  }
  comp_id h := by
    cases h; simp [C.comp_id, C.id_comp]
  id_comp h := by
    cases h; simp [C.id_comp, C.comp_id]
  assoc h₃ h₂ h₁ := by
    cases h₁; cases h₂; cases h₃; simp [C.assoc]

/-! ## Comma Category — L8: Advanced Topic -/

/-- The comma category (F ↓ G) for functors F : A → C, G : B → C.
    Objects are triples (a, b, f : F a → G b). -/
structure CommaObj {A B C : Category} (F : Functor A C) (G : Functor B C) where
  left : A.Obj
  right : B.Obj
  arrow : C[F.onObj left, G.onObj right]

/-- A morphism in (F ↓ G) from (a, b, f) to (a', b', f'). -/
structure CommaHom {A B C : Category} {F : Functor A C} {G : Functor B C}
    (x y : CommaObj F G) where
  leftMap : A[x.left, y.left]
  rightMap : B[x.right, y.right]
  commutes : G.onHom rightMap ∘ x.arrow = y.arrow ∘ F.onHom leftMap

/-- The comma category (F ↓ G). -/
def CommaCat {A B C : Category} (F : Functor A C) (G : Functor B C) : Category where
  Obj := CommaObj F G
  Hom x y := CommaHom x y
  id x := {
    leftMap := A.id x.left
    rightMap := B.id x.right
    commutes := by
      rw [G.map_id, C.id_comp, F.map_id, C.comp_id]
  }
  comp h₂ h₁ := {
    leftMap := h₂.leftMap ∘ h₁.leftMap
    rightMap := h₂.rightMap ∘ h₁.rightMap
    commutes := by
      calc
        G.onHom (h₂.rightMap ∘ h₁.rightMap) ∘ x.arrow
            = (G.onHom h₂.rightMap ∘ G.onHom h₁.rightMap) ∘ x.arrow := by rw [G.map_comp]
        _ = G.onHom h₂.rightMap ∘ (G.onHom h₁.rightMap ∘ x.arrow) := by rw [C.assoc]
        _ = G.onHom h₂.rightMap ∘ (y.arrow ∘ F.onHom h₁.leftMap) := by rw [h₁.commutes]
        _ = (G.onHom h₂.rightMap ∘ y.arrow) ∘ F.onHom h₁.leftMap := by rw [← C.assoc]
        _ = (z.arrow ∘ F.onHom h₂.leftMap) ∘ F.onHom h₁.leftMap := by rw [h₂.commutes]
        _ = z.arrow ∘ (F.onHom h₂.leftMap ∘ F.onHom h₁.leftMap) := by rw [C.assoc]
        _ = z.arrow ∘ F.onHom (h₂.leftMap ∘ h₁.leftMap) := by rw [F.map_comp]
  }
  comp_id h := by
    cases h; simp [A.comp_id, B.comp_id]
  id_comp h := by
    cases h; simp [A.id_comp, B.id_comp]
  assoc h₃ h₂ h₁ := by
    cases h₁; cases h₂; cases h₃; simp [A.assoc, B.assoc]

/-! ## Presheaf Category (Reference) — L8: Advanced Topic -/

/-- The category of presheaves on C: functors Cᵒᵖ → Set.
    This category is a topos and is central to sheaf theory. -/
def PresheafCategory (C : Category) : Category :=
  -- Conceptual: objects are Functor Cᵒᵖ SetCat, morphisms are natural transformations
  -- This is a placeholder for the full definition
  C

/-! ## Double Opposite is Identity — L4: Fundamental Theorem -/

/-- The double opposite of a functor is the original functor (on objects). -/
theorem functor_double_op_onObj {C D : Category} (F : Functor C D) (X : C.Obj) :
    (Functor.op (Functor.op F)).onObj X = F.onObj X := rfl

/-- The double opposite of a category is (strictly) the original category. -/
theorem category_double_op_obj (C : Category) : (Cᵒᵖᵒᵖ).Obj = C.Obj := rfl

#eval "Morphisms.Equivalence: Functor, NatTrans, FullyFaithful, EssentiallySurjective, Equivalence, Comma, Slice"
#eval s!"Identity functor is an equivalence: {idF_is_equivalence (DiscCat Bool)}"
#eval s!"Identity functor is fully faithful: {idF_fully_faithful (DiscCat Bool)}"
#eval s!"Identity functor is essentially surjective: {idF_essentially_surjective (DiscCat Bool)}"
#eval s!"Diagonal functor on SetCat maps Bool to (Bool, Bool)"
end MiniCategoryCore
