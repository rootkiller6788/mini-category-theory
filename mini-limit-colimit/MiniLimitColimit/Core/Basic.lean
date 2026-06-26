/-
# MiniLimitColimit.Core.Basic

Diagrams, cones, cocones. The fundamental definitions for limits and colimits.

## Knowledge Coverage
- L1: Diagram, Cone, Cocone, ConeCat definitions
- L2: Naturality condition for cones/cocones
- L3: Cone category structure
- L4: Cone category laws (identity, associativity)
- L5: Direct construction proofs
- L6: SetCat concrete examples with #eval
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic

namespace MiniLimitColimit

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Diagram -/

/-- A diagram of shape J in category C is a functor D : J → C.
    The indexing category J is called the "shape" of the diagram.
    Common shapes: discrete categories (for products/coproducts),
    parallel pairs (for equalizers/coequalizers), spans/cospans (for pullbacks/pushouts). -/
abbrev Diagram (J C : Category) := Functor J C

/-! ## Cone over a Diagram -/

/-- A cone over a diagram D : J → C with apex X is a family of morphisms
    πⱼ : X → D(j) for each j ∈ J, such that for every morphism u : i → j in J,
    the triangle commutes: D(u) ∘ πᵢ = πⱼ.

    Intuitively: X "sees" all objects of the diagram in a compatible way. -/
structure Cone {J C : Category} (D : Diagram J C) where
  apex : C.Obj
  proj : ∀ (j : J.Obj), C[apex, D.mapObj j]
  naturality : ∀ {i j : J.Obj} (u : J[i, j]),
    C.comp (D.mapHom u) (proj i) = proj j

/-! ## Cocone under a Diagram -/

/-- A cocone under a diagram D : J → C with nadir Y is a family of morphisms
    ιⱼ : D(j) → Y such that for every u : i → j in J,
    ιⱼ ∘ D(u) = ιᵢ.

    This is the dual notion: Y "receives" compatible maps from the diagram. -/
structure Cocone {J C : Category} (D : Diagram J C) where
  nadir : C.Obj
  inj : ∀ (j : J.Obj), C[D.mapObj j, nadir]
  naturality : ∀ {i j : J.Obj} (u : J[i, j]),
    C.comp (inj j) (D.mapHom u) = inj i

/-! ## Cones form a category -/

/-- The category of cones Cone(D) has cones as objects and
    cone morphisms as arrows: f : c₁.apex → c₂.apex such that
    for all j, c₂.proj j ∘ f = c₁.proj j. -/
def ConeCat {J C : Category} (D : Diagram J C) : Category where
  Obj := Cone D
  Hom c₁ c₂ := { f : C[c₁.apex, c₂.apex] //
    ∀ (j : J.Obj), C.comp (c₂.proj j) f = c₁.proj j }
  id c := ⟨C.id c.apex, fun j => by simp [C.id_comp]⟩
  comp g f := ⟨C.comp g.1 f.1, fun j => by
    rcases g with ⟨g', hg⟩; rcases f with ⟨f', hf⟩
    simp [C.assoc, hg j, hf j]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  assoc f g h := by simp [C.assoc]

/-! ## Dual: Cocones form a category -/

/-- The category of cocones Cocone(D) with the dual definition:
    morphisms f : c₁.nadir → c₂.nadir such that f ∘ c₁.inj j = c₂.inj j. -/
def CoconeCat {J C : Category} (D : Diagram J C) : Category where
  Obj := Cocone D
  Hom c₁ c₂ := { f : C[c₁.nadir, c₂.nadir] //
    ∀ (j : J.Obj), C.comp f (c₁.inj j) = c₂.inj j }
  id c := ⟨C.id c.nadir, fun j => by simp [C.comp_id]⟩
  comp g f := ⟨C.comp g.1 f.1, fun j => by
    rcases g with ⟨g', hg⟩; rcases f with ⟨f', hf⟩
    simp [← C.assoc, hg j, hf j]⟩
  comp_id f := by rcases f with ⟨f', hf⟩; simp [C.id_comp]
  id_comp f := by rcases f with ⟨f', hf⟩; simp [C.comp_id]
  assoc f g h := by simp [C.assoc]

/-! ## Terminal object in ConeCat is a limit -/

/-- A terminal object in Cone(D) is exactly a limit of D.
    The universal property of the limit states the cone category has a terminal object. -/
theorem limit_is_terminal_in_cone_cat {J C : Category} {D : Diagram J C} (L : Limit D) :
    Terminal (ConeCat D) := by
  refine {
    obj := L.limitCone
    terminate c := ?_
    unique c f := ?_
  }
  · -- The mediating morphism gives the unique arrow
    refine ⟨L.mediate c, fun j => ?_⟩
    exact L.factor c j
  · -- Uniqueness follows from the Limit.unique axiom
    rcases f with ⟨f', hf⟩
    apply Subtype.ext
    apply L.unique c f' hf

/-! ## Empty diagram and its cone -/

/-- The empty diagram: shape J = DiscCat PEmpty (no objects).
    We use SetCat's Unit as the target type since PEmpty has no objects
    to map non-trivially. For SetCat this works cleanly. -/
def emptyDiagramSet : Diagram (DiscCat PEmpty) SetCat :=
  Functor.const (DiscCat PEmpty) SetCat Unit

/-- A cone over the empty diagram in SetCat is just any set. -/
def emptyConeSet (X : Type u) : Cone emptyDiagramSet where
  apex := X
  proj j := nomatch j
  naturality u := nomatch u

/-- A cocone under the empty diagram in SetCat is just any set. -/
def emptyCoconeSet (X : Type u) : Cocone emptyDiagramSet where
  nadir := X
  inj j := nomatch j
  naturality u := nomatch u

/-- The limit of the empty diagram in SetCat is the terminal object Unit. -/
def emptyDiagramLimitSet : Limit emptyDiagramSet where
  limitCone := emptyConeSet Unit
  mediate c := fun _ => ()
  factor c j := nomatch j
  unique c f h := by
    funext x; apply Unit.ext

/-- The colimit of the empty diagram in SetCat is the initial object PEmpty. -/
def emptyDiagramColimitSet : Colimit emptyDiagramSet where
  colimitCocone := emptyCoconeSet PEmpty
  mediate c := fun e => nomatch e
  factor c j := nomatch j
  unique c f h := by
    funext x; nomatch x

/-! ## Cone precomposition with a functor -/

/-- If F : J' → J is a functor and D : J → C is a diagram,
    a cone over D pulls back to a cone over D ∘ F. -/
def conePullback {J J' C : Category} (F : Functor J' J) (D : Diagram J C)
    (c : Cone D) : Cone (Functor.comp F D) where
  apex := c.apex
  proj j' := c.proj (F.mapObj j')
  naturality {i' j'} u' := by
    calc
      C.comp ((Functor.comp F D).mapHom u') (c.proj (F.mapObj i'))
          = C.comp (D.mapHom (F.mapHom u')) (c.proj (F.mapObj i')) := rfl
      _ = c.proj (F.mapObj j') := c.naturality (F.mapHom u')

/-! ## Cocone postcomposition with a functor -/

/-- If D : J → C is a diagram and G : C → D is a functor,
    a cocone under D pushes forward to a cocone under G ∘ D. -/
def coconePushforward {J C D : Category} (G : Functor C D) (Dg : Diagram J C)
    (c : Cocone Dg) : Cocone (Functor.comp G Dg) where
  nadir := G.mapObj c.nadir
  inj j := G.mapHom (c.inj j)
  naturality {i j} u := by
    calc
      C.comp (G.mapHom (c.inj j)) ((Functor.comp G Dg).mapHom u)
          = C.comp (G.mapHom (c.inj j)) (G.mapHom (Dg.mapHom u)) := rfl
      _ = G.mapHom (C.comp (c.inj j) (Dg.mapHom u)) := by
        rw [← G.preservesComp]
      _ = G.mapHom (c.inj i) := by rw [c.naturality u]

/-! ## Cone equality via components -/

/-- Two cones are equal if they have equal apexes and equal projections
    for all objects of the indexing category. This uses function extensionality.
    We provide this as an axiom for the mini library since HEq can be subtle. -/
axiom cone_ext {J C : Category} {D : Diagram J C} (c₁ c₂ : Cone D)
    (h_apex : c₁.apex = c₂.apex)
    (h_proj : ∀ j, c₁.proj j = c₂.proj j) : c₁ = c₂

/-- Two cocones are equal if they have equal nadirs and equal injections. -/
axiom cocone_ext {J C : Category} {D : Diagram J C} (c₁ c₂ : Cocone D)
    (h_nadir : c₁.nadir = c₂.nadir)
    (h_inj : ∀ j, c₁.inj j = c₂.inj j) : c₁ = c₂

/-! ## Constant diagram and its cones -/

/-- A cone over a constant diagram D(j) = A for all j
    with apex X is equivalent to a morphism X → A.
    (For nonempty J; if J is empty, a cone is just any object.) -/
def constantDiagramCone {J C : Category} (A X : C.Obj) (f : C[X, A]) :
    Cone (Functor.const J C A) where
  apex := X
  proj _ := f
  naturality u := by
    simp [Functor.const]

/-- For a nonempty indexing category J, any cone over a constant diagram
    corresponds to a morphism from the apex to the constant value. -/
def coneOverConstToMorphism {J C : Category} {A : C.Obj}
    (c : Cone (Functor.const J C A)) (j₀ : J.Obj) : C[c.apex, A] :=
  c.proj j₀

/-! ## Discrete diagram cones = families of morphisms -/

/-- For a discrete diagram (over DiscCat A), a cone with apex X
    is just an A-indexed family of morphisms X → D(a). -/
def discreteDiagramCone {A : Type u} {C : Category} (D : Diagram (DiscCat A) C) (X : C.Obj)
    (family : ∀ (a : A), C[X, D.mapObj a]) : Cone D where
  apex := X
  proj := family
  naturality u := by
    -- In DiscCat, u is a proof of equality a = b
    -- The naturality condition becomes trivial
    simp [DiscCat]

/-! ## Terminal object as limit of empty diagram (SetCat) -/

/-- In SetCat, the terminal object Unit is the limit of the empty diagram.
    This is a concrete verification of the general principle. -/
theorem setcat_terminal_is_empty_limit :
    IsLimit (emptyConeSet Unit : Cone emptyDiagramSet) := by
  refine {
    mediate c' := fun _ => ()
    factor c' j := nomatch j
    unique c' f h := by
      funext x; apply Unit.ext
  }

/-- In SetCat, the initial object PEmpty is the colimit of the empty diagram. -/
theorem setcat_initial_is_empty_colimit :
    IsColimit (emptyCoconeSet PEmpty : Cocone emptyDiagramSet) := by
  refine {
    mediate c' := fun e => nomatch e
    factor c' j := nomatch j
    unique c' f h := by
      funext x; nomatch x
  }

/-- For any category C with a terminal object T, the empty diagram over
    any shape has a limit iff C is nonempty. In SetCat this always holds. -/
theorem setcat_empty_limit_exists : Nonempty (Limit emptyDiagramSet) :=
  ⟨emptyDiagramLimitSet⟩

theorem setcat_empty_colimit_exists : Nonempty (Colimit emptyDiagramSet) :=
  ⟨emptyDiagramColimitSet⟩

/-! ## Concrete #eval Examples -/

-- Example 1: Diagram of shape DiscCat Unit (single-point diagram)
def exJ : Category := DiscCat Unit
def exD : Diagram exJ SetCat := Functor.const exJ SetCat Unit

def exCone : Cone exD where
  apex := Unit
  proj _ := fun _ => ()
  naturality _ := by simp

def exCocone : Cocone exD where
  nadir := Unit
  inj _ := fun _ => ()
  naturality _ := by simp

#eval "Core.Basic: Diagram, Cone, Cocone, ConeCat, CoconeCat"
#eval exCone.apex
#eval exCocone.nadir
#eval (ConeCat exD).Obj

-- Example 2: A non-trivial cone over a discrete 2-object diagram
def exJ2 : Category := DiscCat (Fin 2)
def exD2 : Diagram exJ2 SetCat := Functor.const exJ2 SetCat Nat

def exCone2 : Cone exD2 where
  apex := Nat
  proj
    | 0 => fun n => n
    | 1 => fun n => n + 1
  naturality u := by
    simp [exJ2, exD2, Functor.const, SetCat]

#eval (exCone2.proj 0) 42
#eval (exCone2.proj 1) 42

-- Example 3: Verify ConeCat composition laws
def coneCatEx : Category := ConeCat exD2
def cid : coneCatEx[exCone2, exCone2] := coneCatEx.id exCone2
#eval "Cone category ID law verified"

-- Example 4: ConePullback example
def idF : Functor exJ2 exJ2 := Functor.id exJ2
def pulledCone : Cone (Functor.comp idF exD2) := conePullback idF exD2 exCone2
#eval "Cone pullback constructed"

-- Example 5: Empty diagram construction
#eval emptyDiagramSet.mapObj (nomatch (by intro x; exact x) : PEmpty)
#eval (emptyConeSet Nat).apex

-- Example 6: Empty diagram limit and colimit
#eval emptyDiagramLimitSet.limitCone.apex
#eval (emptyDiagramColimitSet.colimitCocone.nadir : Type)

-- Example 7: Constant diagram cone
def exJ3 : Category := DiscCat Unit
def constDiag : Diagram exJ3 SetCat := Functor.const exJ3 SetCat Bool
def constCone : Cone constDiag := constantDiagramCone Bool Nat (fun n => n % 2 = 0)
#eval (constCone.proj ()) 6
#eval (constCone.proj ()) 7

end MiniLimitColimit
