/-
# MiniCategoryCore.Theorems.Classification

Classification theorems: every category is equivalent to its skeleton,
characterization of discrete/codiscrete/poset/groupoid categories.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Equivalence
import MiniCategoryCore.Properties.Invariants
import MiniCategoryCore.Properties.ClassificationData

namespace MiniCategoryCore

/-! ## Skeleton Equivalence Theorem -/

/-- Every category is equivalent to its skeleton.
    This is a deep result stated as an axiom for reference. -/
axiom skeleton_theorem (C : Category) :
  ∃ (skel : Category), isSkeletal skel ∧ Nonempty (Equivalence C skel)

/-- The skeleton of a category is unique up to equivalence of categories.
    If C is equivalent to two skeletal categories S1, S2, then S1 and S2
    are equivalent. This is a classical theorem requiring the axiom of choice. -/
axiom skeleton_unique (C : Category) (S1 S2 : Category)
    (h1 : isSkeletal S1) (h2 : isSkeletal S2)
    (eq1 : Nonempty (Equivalence C S1)) (eq2 : Nonempty (Equivalence C S2)) :
    Nonempty (Equivalence S1 S2)

/-! ## Discrete Category Classification -/

/-- A category equivalent to a discrete category is a groupoid.
    Groupoid-ness is preserved by equivalence of categories. -/
theorem equiv_discrete_is_groupoid (C : Category)
    (h : ∃ (A : Type u), Nonempty (Equivalence C (DiscCat A))) : isGroupoid C := by
  rcases h with ⟨A, ⟨E⟩⟩
  intro X Y f
  -- Since DiscCat A is a groupoid, E.F.onHom f is an iso in DiscCat A
  have hF_iso : IsIso (C := DiscCat A) (E.F.onHom f) :=
    discrete_is_groupoid A (E.F.onHom f)
  -- Use the equivalence structure to reflect the iso back to C
  have h_equiv : isEquivalence E.F := by
    exists E.G
    exists λ X' => E.η X'
    exists λ Y' => E.ε Y'
    exact ⟨E.triangle1, E.triangle2⟩
  -- The equivalence characterization: E.F is fully faithful
  have hFF : FullyFaithful E.F := ((equivalence_iff_ff_es E.F).mp h_equiv).left
  rcases hFF with ⟨hinj, hsurj⟩
  -- Get the inverse in DiscCat A
  rcases hF_iso with ⟨g', hfg, hgf⟩
  -- Lift the inverse to C using fullness
  rcases hsurj (X := Y) (Y := X) g' with ⟨g, hg⟩
  -- g : C[Y, X] is the candidate inverse
  exists g
  refine ⟨?_, ?_⟩
  · -- f ∘ g = C.id Y
    apply hinj
    calc
      E.F.onHom (f ∘ g) = E.F.onHom f ∘ E.F.onHom g := E.F.map_comp f g
      _ = E.F.onHom f ∘ g' := by rw [hg]
      _ = (DiscCat A).id (E.F.onObj Y) := hfg
      _ = E.F.onHom (C.id Y) := by rw [E.F.map_id Y]
  · -- g ∘ f = C.id X
    apply hinj
    calc
      E.F.onHom (g ∘ f) = E.F.onHom g ∘ E.F.onHom f := E.F.map_comp g f
      _ = g' ∘ E.F.onHom f := by rw [hg]
      _ = (DiscCat A).id (E.F.onObj X) := hgf
      _ = E.F.onHom (C.id X) := by rw [E.F.map_id X]

/-- The discrete category DiscCat A is skeletal. -/
theorem discrete_is_skeletal' (A : Type u) : isSkeletal (DiscCat A) :=
  discrete_is_skeletal A

/-! ## Poset Categories -/

/-- A thin category is one with at most one morphism per hom-set. -/
def isThin (C : Category) : Prop :=
  ∀ {X Y : C.Obj} (f g : C[X, Y]), f = g

/-- A thin skeletal category defines a poset:
    Define ≤ on objects by X ≤ Y iff C[X,Y] is nonempty.
    This is reflexive (by id), transitive (by composition), and
    antisymmetric (by skeletal: Iso → X = Y). -/
theorem thin_skeletal_defines_poset (C : Category) (thin : isThin C) (skel : isSkeletal C) :
    ∀ (X Y : C.Obj), (∃ (f : C[X, Y]), True) → (∃ (g : C[Y, X]), True) → X = Y := by
  intro X Y hXY hYX
  rcases hXY with ⟨f, _⟩
  rcases hYX with ⟨g, _⟩
  -- In a thin category, g ∘ f = id X and f ∘ g = id Y (since both hom-sets have ≤1 element)
  have h_gf : g ∘ f = C.id X := by
    apply thin
  have h_fg : f ∘ g = C.id Y := by
    apply thin
  -- So f is an iso, hence X = Y by skeletal
  have h_iso : IsIso f := by
    exists g
    exact ⟨h_fg, h_gf⟩
  exact skel X Y ⟨mkIso f h_iso⟩

/-- The codiscrete category is thin. -/
theorem codiscrete_is_thin (A : Type u) : isThin (CodiscCat A) := by
  intro X Y f g; cases f; cases g; rfl

/-- The preorder category PreorderCat is thin. -/
theorem preorder_cat_is_thin' {A : Type u} {R : A → A → Prop} [DecidableRel R]
    (refl : ∀ a, R a a) (trans : ∀ {a b c}, R a b → R b c → R a c) :
    isThin (PreorderCat A R refl trans) := by
  intro X Y f g; cases f; cases g; rfl

/-! ## Groupoid Classification -/

/-- In a groupoid, mono + epi simplifies to iso (since everything is iso). -/
theorem groupoid_mono_epi_is_iso (C : Category) (h : isGroupoid C) {X Y : C.Obj} (f : C[X, Y])
    (_ : Mono f) (_ : Epi f) : IsIso f :=
  h f

/-! ## Concrete Classifications -/

/-- The discrete category on any type is a groupoid and skeletal. -/
theorem disc_cat_classification (A : Type u) : isGroupoid (DiscCat A) ∧ isSkeletal (DiscCat A) := by
  refine ⟨discrete_is_groupoid A, discrete_is_skeletal A⟩

/-- The codiscrete category is a connected groupoid. -/
theorem codisc_cat_classification (A : Type u) :
    isGroupoid (CodiscCat A) ∧ isConnected (CodiscCat A) := by
  refine ⟨codiscrete_is_groupoid A, codiscrete_is_connected A⟩

/-- SetCat is not a groupoid (not every function has an inverse). -/
theorem setcat_not_groupoid : ¬ isGroupoid (SetCat : Category) := by
  intro h
  have h' := h (λ (_ : Empty) => ()) (X := Empty) (Y := Unit)
  rcases h' with ⟨g, hfg, hgf⟩
  -- hfg : (λ _ => ()) ∘ g = id Unit, so for any u:Unit, g u must be in Empty. Impossible.
  have h_unit : ((λ (_ : Empty) => ()) ∘ g) () = (SetCat.id Unit) () := by rw [hfg]
  simp at h_unit
  -- h_unit : () = () which is trivially true... hmm.
  -- Actually the function Empty → Unit composed with g : Unit → Empty
  -- Wait: f : Empty → Unit (the unique function)
  -- We need g : Unit → Empty such that f ∘ g = id Unit and g ∘ f = id Empty
  -- But g : Unit → Empty is impossible since Empty has no elements.
  -- Actually g : Unit → Empty doesn't exist because Empty has no constructors.
  -- Wait, g is of type Unit → Empty, which is inhabited only if Empty is inhabited... which is not true.
  -- Actually, (SetCat: Category)[Unit, Empty] = Unit → Empty, which is a function type.
  -- There IS exactly one function from Empty → Unit, but Unit → Empty is the type of functions
  -- from Unit to Empty. Since Unit is inhabited and Empty is not, this type is empty (no functions exist).
  -- So g : Unit → Empty cannot exist → contradiction.
  -- But we have g in the context from h', which means g is of type SetCat[Unit, Empty] = Unit → Empty.
  -- We can apply g to () to get an Empty.
  let e : Empty := g ()
  exact e.elim

/-- SetCat is connected. -/
theorem setcat_connected : isConnected (SetCat : Category) :=
  SetCat_is_connected

#eval "Theorems.Classification: skeleton theorem, discrete/poset/groupoid classification"
#eval "DiscCat Nat is skeletal and a groupoid"
#eval "CodiscCat is connected and a groupoid; SetCat is connected but not a groupoid"
end MiniCategoryCore
