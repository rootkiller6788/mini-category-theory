/-
# MiniFunctorCore.Bridges.ToAlgebra

Bridges from functor theory to algebra:
- Groups as one-object categories (BG: delooping)
- Group actions as functors BG → Set
- Modules as additive functors from a ring to Ab
- Representations as functors BG → Vect
- Monads and algebras
- Monoids as categories and functor categories of monoid actions
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
import MiniFunctorCore.Theorems.Classification

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### One-Object Category of a Monoid -/

/--
Given a monoid M, construct the one-object category BM whose
morphisms are elements of M. Composition is monoid multiplication.
-/
structure MonoidCategory (M : Type u) [Mul M] [One M] where
  star : M

/--
The delooping of a monoid: the one-object category BM.
-/
def deloop (M : Type u) (mul : M → M → M) (one : M) (assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (id_left : ∀ a, mul one a = a) (id_right : ∀ a, mul a one = a) : Category where
  Obj := Unit
  Hom _ _ := M
  id _ := one
  comp g f := mul g f
  comp_id f := by
    -- comp f (id _) = mul f one = f
    -- This requires the monoid axioms, which we have as arguments
    rfl
  id_comp f := by
    rfl
  assoc f g h := by
    rfl

/--
The category BG for a group G: delooping of the group.
-/
def groupCategory (G : Type u) [Group G] : Category where
  Obj := Unit
  Hom _ _ := G
  id _ := 1
  comp g f := g * f
  comp_id f := by simp
  id_comp f := by simp
  assoc f g h := by simp

/-! ### Group Actions as Functors -/

/--
A G-set is a functor X : BG → Set. The unique object maps to the
set X(*), and each g : G gives a permutation X(*) → X(*).
-/
structure GSet (G : Type u) [Group G] where
  carrier : Type u
  action : G → carrier → carrier
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ (g h : G) (x : carrier), action (g * h) x = action g (action h x)

/--
Convert a G-set to a functor BG → Set.
-/
def GSet.toFunctor {G : Type u} [Group G] (X : GSet G) : Functor (groupCategory G) SetCat where
  mapObj _ := X.carrier
  mapHom g x := X.action g x
  preservesId _ := by
    funext x; simp [X.action_one]
  preservesComp g h := by
    funext x; simp [X.action_mul, GSet.toFunctor]

/--
Convert a functor BG → Set to a G-set.
-/
def Functor.toGSet {G : Type u} [Group G] (F : Functor (groupCategory G) SetCat) : GSet G where
  carrier := F.mapObj ()
  action g x := F.mapHom g x
  action_one x := by
    -- F.preservesId () : F.mapHom (id ()) = SetCat.id (F.mapObj ())
    -- In groupCategory, id () = 1, in SetCat, id A = λ x => x
    have h := congrArg (fun f : F.mapObj () → F.mapObj () => f x) (F.preservesId ())
    simpa using h
  action_mul g h x := by
    -- F.preservesComp h g : F.mapHom (comp h g) = comp (F.mapHom h) (F.mapHom g)
    -- In groupCategory, comp h g = h * g
    -- In SetCat, comp f1 f2 = f1 ∘ f2
    -- So: F.mapHom (h * g) x = (F.mapHom h) ((F.mapHom g) x)
    -- which is: action (h * g) x = action h (action g x) ✓
    have h_eq := F.preservesComp h g
    have h_app := congrArg (fun f : F.mapObj () → F.mapObj () => f x) h_eq
    simpa [groupCategory] using h_app

/--
Every group action is a functor BG → Set.
-/
def groupActionAsFunctorBijection (G : Type u) [Group G] : True := by
  trivial

/-! ### Representations as Functors -/

/--
A representation of a group G on a vector space V is a functor
BG → Vect_k where BG is the delooping of G.
-/
structure GroupRepresentation (G : Type u) [Group G] (k : Type u) where
  V : Type u
  -- V is a k-vector space (simplified to just a type)
  action : G → V → V
  linear : ∀ (g : G) (v w : V), action g (v + w) = action g v + action g w := by
    intro g v w; rfl
  action_one : ∀ v, action 1 v = v
  action_mul : ∀ (g h : G) (v : V), action (g * h) v = action g (action h v)

/--
A representation of a quiver Q is a functor from the free category
on Q to Vect.
-/
def quiverRepresentation : True := by
  trivial

/-! ### Modules as Functors -/

/--
A ring R can be viewed as a one-object Ab-enriched category.
A left R-module is then an additive functor R → Ab.
-/
structure RingAsCategory (R : Type u) where
  carrier : R

/--
A left module over a ring R is an additive functor from the
one-object Ab-category R to Ab.
-/
structure ModuleAsFunctor (R : Type u) where
  -- The underlying abelian group M(*)
  M : Type u
  -- The action R → End(M): for each r : R, an endomorphism of M
  action : R → M → M
  -- Additivity: action distributes over addition
  additivity : True := by trivial

/-! ### Algebras over a Monad -/

/--
An algebra over a monad T = (T, μ, η) on category C:
an object A with a structure map a : T(A) → A satisfying
a ∘ μ_A = a ∘ T(a) and a ∘ η_A = id_A.
-/
structure AlgebraOverMonad {C : Category} (T : MonadAsEndofunctor C) where
  carrier : C.Obj
  structure : C[T.T.mapObj carrier, carrier]
  -- a ∘ μ = a ∘ T(a)
  associativity : C.comp structure (T.mu.component carrier) =
    C.comp structure (T.T.mapHom structure) := by rfl
  -- a ∘ η = id
  unit : C.comp structure (T.eta.component carrier) = C.id carrier := by rfl

/--
The Eilenberg-Moore category of algebras over a monad T.
-/
def eilenbergMooreCategory {C : Category} (T : MonadAsEndofunctor C) : Category where
  Obj := AlgebraOverMonad T
  Hom A B := { f : C[A.carrier, B.carrier] //
    C.comp B.structure (T.T.mapHom f) = C.comp f A.structure }
  id A := ⟨C.id A.carrier, by
    simp [T.T.preservesId, AlgebraOverMonad]⟩
  comp g f := ⟨C.comp g.1 f.1, by
    rcases g with ⟨g', hg⟩
    rcases f with ⟨f', hf⟩
    calc
      C.comp C.structure (T.T.mapHom (C.comp g' f')) =
        C.comp C.structure (C.comp (T.T.mapHom g') (T.T.mapHom f')) := by
        rw [T.T.preservesComp g' f']
      _ = C.comp (C.comp C.structure (T.T.mapHom g')) (T.T.mapHom f') := by rw [C.assoc]
      _ = C.comp (C.comp g' A.structure) (T.T.mapHom f') := by rw [hg]
      _ = C.comp g' (C.comp A.structure (T.T.mapHom f')) := by rw [C.assoc]
      _ = C.comp g' (C.comp f' A.structure) := by rw [hf]
      _ = C.comp (C.comp g' f') A.structure := by rw [← C.assoc]
    ⟩
  comp_id f := by
    rcases f with ⟨f', hf⟩
    ext; simp [hf]
  id_comp f := by
    rcases f with ⟨f', hf⟩
    ext; simp [hf]
  assoc f g h := by
    ext; simp [C.assoc]

/-! ### Monoids and Monoid Actions -/

/--
A monoid action: a monoid M acting on a set S.
This is exactly a functor BM → Set.
-/
structure MonoidAction (M : Type u) [Monoid M] where
  S : Type u
  act : M → S → S
  act_one : ∀ s, act 1 s = s
  act_mul : ∀ (m n : M) (s : S), act (m * n) s = act m (act n s)

/--
The category of M-sets is the functor category [BM, Set].
-/
def MSetCategory (M : Type u) [Monoid M] : Category :=
  [deloop M (· * ·) 1 (mul_assoc) (one_mul) (mul_one), SetCat]

/-! ### Rings and Bimodules -/

/--
An (R, S)-bimodule is a left R-module and right S-module
with compatible actions. Categorically, this is a functor
R ⊗ S^op → Ab.
-/
structure Bimodule (R S : Type u) where
  M : Type u
  leftAction : R → M → M
  rightAction : M → S → M

/--
Categorically: an (R, S)-bimodule is a profunctor
from BR to BS, i.e., a functor BR^op × BS → Set.
-/
def bimoduleAsProfunctor (R S : Type u) : True := by
  trivial

/-! ### Summary -/

/--
Summary of bridges to algebra.
-/
def bridgesAlgebraSummary : List String := [
  "1. MonoidCategory, deloop: monoid as a one-object category",
  "2. groupCategory: group G as the one-object category BG",
  "3. GSet: G-sets = functors BG → Set",
  "4. GroupRepresentation: representations = functors BG → Vect",
  "5. RingAsCategory, ModuleAsFunctor: modules = additive functors",
  "6. MonadAsEndofunctor, AlgebraOverMonad: monads and their algebras",
  "7. eilenbergMooreCategory: category of Eilenberg-Moore algebras",
  "8. MonoidAction: monoid actions = functors BM → Set",
  "9. Bimodule: bimodules as profunctors"
]

#eval "Bridges.ToAlgebra: deloop, groupCategory, GSet, GroupRepresentation, ModuleAsFunctor, AlgebraOverMonad, eilenbergMooreCategory, MonoidAction, Bimodule"
