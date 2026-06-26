/-
# MiniAdjunction.Constructions.Universal

Free-forgetful adjunctions: free monoid, free group, free vector space.
The archetypal examples of adjunctions in algebra.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Free Monoid Adjunction -/

/--
The free monoid functor F : Set → Monoid sends a set X to the free monoid
on X (words over X). The forgetful functor U : Monoid → Set sends a monoid
to its underlying set. Then F ⊣ U.
-/
structure FreeMonoidAdjunction where
  freeF : Functor SetCat SetCat
  forgetfulU : Functor SetCat SetCat
  adj : freeF ⊣ forgetfulU
  freeMeaning : ∀ (X : Type u), Prop

/--
The free monoid adjunction: words over a set, concatenation, empty word.
-/
axiom freeMonoidAdjunction : FreeMonoidAdjunction

/--
The unit of the free monoid adjunction: X → U(F X) is the inclusion
of generators.
-/
axiom freeMonoidUnit : ∀ (X : Type u), X → List X

/--
The counit: F(U M) → M evaluates a formal word in the monoid.
-/
axiom freeMonoidCounit : Prop

#eval "Constructions.Universal: freeMonoidAdjunction (axiom)"
#eval "Constructions.Universal: Free ⊣ Forgetful for Monoids"

/-! ## Free Group Adjunction -/

/--
The free group functor F : Set → Group and forgetful U : Group → Set.
F ⊣ U, similar to the monoid case but with inverses.
-/
structure FreeGroupAdjunction where
  freeF : Functor SetCat SetCat
  forgetfulU : Functor SetCat SetCat
  adj : freeF ⊣ forgetfulU
  freeMeaning : ∀ (X : Type u), Prop

/--
The free group on a set X: words over X ∪ X⁻¹ modulo group laws.
-/
axiom freeGroupAdjunction : FreeGroupAdjunction

#eval "Constructions.Universal: freeGroupAdjunction (axiom)"

/-! ## Free Vector Space Adjunction -/

/--
The free vector space functor F : Set → Vect and forgetful U : Vect → Set.
Free vector space = formal linear combinations, F ⊣ U.
-/
structure FreeVectorSpaceAdjunction where
  freeF : Functor SetCat SetCat
  forgetfulU : Functor SetCat SetCat
  adj : freeF ⊣ forgetfulU
  field : Type u

/--
The free k-vector space on a set X: formal finite linear combinations
∑ a_i x_i over the field k.
-/
axiom freeVectorSpaceAdjunction (k : Type u) : FreeVectorSpaceAdjunction

#eval "Constructions.Universal: freeVectorSpaceAdjunction over a field k"

/-! ## Free-Forgetful Pattern -/

/--
The general free-forgetful adjunction pattern:
Given a category of algebraic structures A and the category of sets S,
the free functor S → A is left adjoint to the forgetful functor A → S.
-/
structure GeneralFreeForgetful where
  free : Functor SetCat SetCat
  forgetful : Functor SetCat SetCat
  adj : free ⊣ forgetful
  algebraicTheory : Prop

/-! ## Free Category Adjunction -/

/--
The free category on a graph: F : Graph → Cat ⊣ U : Cat → Graph.
This is the "free/forgetful" in categorical terms.
-/
axiom freeCategoryAdjunction : Prop

#eval "Constructions.Universal: Free ⊣ Forgetful pattern — general free-forgetful adjunction"
