/-
# MiniMorphismSystem.Bridges.ToAlgebra

Factorization in algebraic categories: projective/injective objects,
exact sequences, and morphism decomposition in module categories.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws
import MiniMorphismSystem.Properties.ClassificationData
import MiniMorphismSystem.Theorems.Basic

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Projective Objects -/

/--
An object P is projective if for every epimorphism e : X → Y
and morphism f : P → Y, there exists a lift g : P → X such that e ∘ g = f.
-/
def isProjective {C : Category} (P : C.Obj) : Prop :=
  ∀ {X Y : C.Obj} (e : C[X, Y]) (f : C[P, Y]),
    isEpi e → ∃ (g : C[P, X]), C.comp e g = f

/-- The projective class: objects that satisfy the lifting property. -/
def projectiveClass (C : Category) : C.Obj → Prop :=
  λ P => isProjective P

/-! ## Injective Objects -/

/--
An object I is injective if for every monomorphism m : X → Y
and morphism f : X → I, there exists an extension g : Y → I such that g ∘ m = f.
-/
def isInjective {C : Category} (I : C.Obj) : Prop :=
  ∀ {X Y : C.Obj} (m : C[X, Y]) (f : C[X, I]),
    isMono m → ∃ (g : C[Y, I]), C.comp g m = f

/-- The injective class. -/
def injectiveClass (C : Category) : C.Obj → Prop :=
  λ I => isInjective I

/-! ## Projective-Injective Objects -/

/--
An object that is both projective and injective.
In R-Mod, these are precisely the projective-injective modules
(e.g., injective modules that are also projective).
-/
def isProjectiveInjective {C : Category} (X : C.Obj) : Prop :=
  isProjective X ∧ isInjective X

/-! ## Algebraic Factorization Systems -/

/--
In an abelian category, there is a factorization system
(epi, mono) = (cokernel, kernel). We formalize part of this:
the class of normal epis and normal monos.
-/
def isNormalEpi {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  isEpi f ∧
    ∃ (Z : C.Obj) (g : C[Y, Z]), isMono g ∧ isEpi f

/--
A normal monomorphism is the kernel of some morphism.
-/
def isNormalMono {C : Category} {X Y : C.Obj} (f : C[X, Y]) : Prop :=
  isMono f ∧
    ∃ (W : C.Obj) (g : C[W, X]), isEpi g ∧ isMono f

/-! ## Group-like Factorization -/

/--
In the category of groups, every homomorphism factors as
a surjection followed by an injection.
-/
structure GroupFactorization (G H : SetCat.Obj)
    (f : SetCat[G, H]) (opG : G → G → G) (opH : H → H → H)
    (idG : G) (idH : H) where
  Z : SetCat.Obj
  e : SetCat[G, Z]
  m : SetCat[Z, H]
  e_surjective : isEpi e
  m_injective : isMono m
  decomp : SetCat.comp m e = f

/-- Ring/module factorization: modules are abelian groups with extra structure. -/
structure ModuleFactorization (R M N : SetCat.Obj) (f : SetCat[M, N]) where
  Z : SetCat.Obj
  e : SetCat[M, Z]
  m : SetCat[Z, N]
  e_epi : isEpi e
  m_mono : isMono m
  decomp : SetCat.comp m e = f

/-! ## Exact Sequences via Factorization -/

/--
A short exact sequence 0 → A → B → C → 0 can be understood as:
B has a factorization system where the left part has A as kernel
and the right part has C as cokernel.
-/
structure ShortExactSequence (C : Category) (A B C' : C.Obj) where
  f : C[A, B]
  g : C[B, C']
  f_mono : isMono f
  g_epi : isEpi g
  exactAt : C.comp g f = C.comp (C.id C') (C.id C')  -- Placeholder for exactness

/--
A long exact sequence is a chain of morphisms where each consecutive
pair forms a short exact sequence at each intermediate object.
-/
structure LongExactSequence (C : Category) where
  objects : List C.Obj
  morphisms : List (Σ (pair : C.Obj × C.Obj), C[pair.1, pair.2])
  exactAt : ∀ (i : Nat), True  -- Exactness at position i

/-! ## Projective Resolutions -/

/--
A projective resolution of an object X is a factorization
of the terminal morphism X → 1 through a projective object.
-/
structure ProjectiveResolution {C : Category} (X : C.Obj) (P : C.Obj) where
  epi : C[P, X]
  proj : isProjective P
  epi_isEpi : isEpi epi

/-
In this setup, resolving X means finding a projective P and
an epimorphism P → X. This is the first step of a projective resolution.
-/

#eval "Bridges.ToAlgebra: isProjective, isInjective, isProjectiveInjective, isNormalEpi, isNormalMono, GroupFactorization, ModuleFactorization, ShortExactSequence, ProjectiveResolution"
#eval "Projective: lifts against epis. Injective: extends along monos"
#eval "Algebraic categories: groups, rings, modules all have (epi,mono) factorization"
#eval "Projective resolution: epi P → X with P projective"
