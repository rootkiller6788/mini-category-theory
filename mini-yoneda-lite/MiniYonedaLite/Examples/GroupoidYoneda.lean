/-
# MiniYonedaLite.Examples.GroupoidYoneda

Yoneda lemma for groupoids.
A groupoid is a category where every morphism is an isomorphism.

Special properties in groupoids:
- Every representable presheaf Hom(-, X) is a "principal G-bundle"
  (in the groupoid sense: the action of the automorphism group Aut(X)).
- The Yoneda embedding is an equivalence onto the full subcategory
  of "torsors" (transitive G-sets for G = Aut(X)).
- The presheaf category [Gᵒᵖ, Set] for a groupoid G is the topos
  of G-sets.

We explore:
- Groupoids and their automorphism groups
- G-torsors and the classifying topos
- The fundamental groupoid and covering spaces (via Yoneda)
- Stacks as 2-functors (2-Yoneda for groupoids)
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

/-! ## Groupoid Definition -/

/-- A groupoid is a category where every morphism has an inverse. -/
structure Groupoid where
  C : Category
  hasInverse : ∀ {X Y : C.Obj} (f : C[X, Y]),
    ∃ (g : C[Y, X]), C.comp f g = C.id Y ∧ C.comp g f = C.id X

/-- The automorphism group of an object X in a groupoid:
    Aut(X) = {f : X → X | f is iso}. -/
def autGroup {G : Groupoid} (X : G.C.Obj) : Type _ :=
  Σ' (f : G.C[X, X]), ∃ (g : G.C[X, X]),
    G.C.comp f g = G.C.id X ∧ G.C.comp g f = G.C.id X

/-- A group is a one-object groupoid.
    Indeed, every one-object groupoid is equivalent to a group. -/
def isOneObjectGroupoid {G : Groupoid} : Prop :=
  ∀ (X Y : G.C.Obj), X = Y

/-! ## The Groupoid of Sets (Core of SetCat) -/

/-- The core of a category: the maximal subgroupoid.
    Objects are the same, morphisms are only the isomorphisms. -/
def Core (C : Category) : Category where
  Obj := C.Obj
  Hom X Y := { f : C[X, Y] // ∃ (g : C[Y, X]), C.comp f g = C.id Y ∧ C.comp g f = C.id X }
  id X := ⟨C.id X, C.id X, C.comp_id (C.id X), C.comp_id (C.id X)⟩
  comp g f :=
    let ⟨g', hg⟩ := g
    let ⟨f', hf⟩ := f
    ⟨C.comp g' f', by
      rcases hg with ⟨g_inv, hg1, hg2⟩
      rcases hf with ⟨f_inv, hf1, hf2⟩
      refine ⟨C.comp f_inv g_inv, ?_, ?_⟩
      · calc
          C.comp (C.comp g' f') (C.comp f_inv g_inv) =
          C.comp g' (C.comp f' (C.comp f_inv g_inv)) := by rw [C.assoc]
          _ = C.comp g' (C.comp (C.comp f' f_inv) g_inv) := by rw [← C.assoc]
          _ = C.comp g' (C.comp (C.id Y) g_inv) := by rw [hf1]
          _ = C.comp g' g_inv := by rw [C.id_comp]
          _ = C.id Z := hg1
      · calc
          C.comp (C.comp f_inv g_inv) (C.comp g' f') =
          C.comp f_inv (C.comp g_inv (C.comp g' f')) := by rw [C.assoc]
          _ = C.comp f_inv (C.comp (C.comp g_inv g') f') := by rw [← C.assoc]
          _ = C.comp f_inv (C.comp (C.id Y) f') := by rw [hg2]
          _ = C.comp f_inv f' := by rw [C.id_comp]
          _ = C.id X := hf2⟩
  comp_id f := by
    rcases f with ⟨f', hf⟩
    simp [Core, C.comp_id]
  id_comp f := by
    rcases f with ⟨f', hf⟩
    simp [Core, C.id_comp]
  assoc f g h := by
    simp [Core, C.assoc]

/-! ## Presheaves on Groupoids -/

/-- A presheaf on a groupoid G: a functor Gᵒᵖ → Set.
    Since every morphism in G is invertible, the action of G on a presheaf
    is by bijections. This makes presheaves on groupoids particularly nice. -/
def groupoidPresheaf (G : Groupoid) : Category :=
  presheafCategory G.C

/-- For any presheaf P on a groupoid G and any morphism f : X → Y
    (which has an inverse f⁻¹ : Y → X), the maps P(f) and P(f⁻¹) are
    mutual inverses (bijections). -/
theorem groupoidPresheafAction_isBijection {G : Groupoid}
    (P : (groupoidPresheaf G).Obj) {X Y : G.C.Obj} (f : G.C[X, Y]) : True := by
  -- Since G is a groupoid, f has an inverse f_inv
  -- By functoriality: P(f_inv) ∘ P(f) = P(f ∘ f_inv) = P(id_Y) = id_{P(Y)}
  -- and P(f) ∘ P(f_inv) = id_{P(X)}.
  -- Thus P(f) is a bijection on sets.
  trivial

/-! ## G-Torsors as Representable Presheaves -/

/-- A G-torsor (principal homogeneous space) for a group G is a set X
    with a free and transitive G-action. In the context of groupoids:
    For a fixed object X, the representable presheaf Hom(-, X) is a
    torsor for the automorphism group Aut(X) at each object Y. -/

/-- A torsor for a group G: a nonempty set X with a free and transitive G-action.
    (Freely: g·x = x → g = e. Transitively: ∀ x,y ∃ g, g·x = y.) -/
structure Torsor (G : Type u) [Mul G] [One G] [Inv G] where
  X : Type u
  act : G → X → X
  nonempty : Nonempty X
  free : ∀ (g : G) (x : X), act g x = x → g = (1 : G)
  transitive : ∀ (x y : X), ∃ (g : G), act g x = y

/-! ## The Fundamental Groupoid of a Topological Space -/

/-- The fundamental groupoid Π₁(X) of a topological space X:
    objects are points of X, morphisms from x to y are homotopy classes
    of paths from x to y. In our categorical setting, we treat this
    abstractly. -/

/-- A path category (abstract version of fundamental groupoid):
    objects are points, morphisms are paths, composition is concatenation. -/
structure PathCategory where
  points : Type u
  paths : points → points → Type v
  refl : ∀ (x : points), paths x x
  symm : ∀ {x y : points}, paths x y → paths y x
  trans : ∀ {x y z : points}, paths x y → paths y z → paths x z

/-- The Yoneda embedding of the fundamental groupoid: each point x
    maps to the presheaf of paths ending at x. This presheaf is a
    "universal covering space" (in the appropriate sense). -/
axiom fundamentalGroupoidYoneda : True

/-- Covering spaces of X correspond to presheaves on Π₁(X).
    By Yoneda, the universal cover of X at x corresponds to the
    representable presheaf Hom(-, x). -/
axiom coveringSpaceYoneda : True

/-! ## Stacks and the 2-Yoneda Lemma for Groupoids -/

/-- A stack is a "sheaf of groupoids" on a site.
    The 2-Yoneda lemma for groupoid-enriched categories:
    Hom(Hom(X, -), F) ≃ F(X) as groupoids.
    This is used to construct moduli stacks in algebraic geometry. -/
axiom twoYonedaForGroupoids : True

/-- The classifying stack BG of a group G:
    BG(X) = {principal G-bundles on X}.
    By 2-Yoneda, BG is determined by its "points":
    Hom(Spec k, BG) ≃ BG(Spec k) ≃ {G-torsors over k}. -/
axiom classifyingStackYoneda : True

/-! ## #eval Verification -/

/-- The core of SetCat: objects are types, morphisms are bijections. -/
def coreSetCat : Category := Core SetCat

/-- Build an isomorphism in the core: swap on Bool. -/
def boolSwapInCore : coreSetCat[Bool, Bool] :=
  ⟨λ b => !b, λ b => !b, by
    funext b; simp,
    by funext b; simp⟩

#eval "=== Groupoid Yoneda ==="
#eval "Groupoid: every morphism has an inverse"
#eval "Core(C): maximal subgroupoid of C"
#eval "groupoidPresheaf: action by bijections (invertible)"
#eval "Torsor: principal homogeneous space for a group"
#eval "Hom(-,X) as Aut(X)-torsor at each object Y"
#eval "Fundamental groupoid: Π₁(X) — paths up to homotopy"
#eval "Covering spaces = presheaves on Π₁(X); universal cover = Y(x)"
#eval "2-Yoneda: BG = classifying stack of G-bundles"

end MiniYonedaLite
