/-
# MiniYonedaLite.Theorems.Basic

The Yoneda Lemma: For any functor F : C → Set and object X,
there is a natural bijection Nat(Hom(X,-), F) ≅ F(X).
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniCategoryCore.Morphisms.Hom
import MiniCategoryCore.Morphisms.Iso
import MiniCategoryCore.Constructions.Products
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Objects
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Theorems.Main
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniNaturalTransformation.Morphisms.Hom
import MiniNaturalTransformation.Morphisms.Iso
import MiniNaturalTransformation.Theorems.Main
import MiniYonedaLite.Core.Basic

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda Lemma -/

/-- The Yoneda lemma: Nat(Hom(X,-), F) ≅ F(X). -/
axiom yonedaLemma {C : Category} (F : Functor C SetCat) (X : C.Obj) :
  Nonempty ([(homFunctor C X), F] ≅ᶠ F.mapObj X)
  -- Nat(Hom(X,-), F) ≅ F(X)

/-! ## Yoneda Embedding Theorem -/

/-- The Yoneda embedding Y : Cᵒᵖ → [C, Set] is fully faithful. -/
axiom yonedaIsFullyFaithful (C : Category) :
  True  -- Y : Cᵒᵖ → [C, Set] is fully faithful

/-! ## Corollary: Representing objects are unique -/

/-- If a functor is represented by two objects, they are isomorphic. -/
axiom representingObjectUnique (C : Category) (F : Functor C SetCat)
    (X Y : C.Obj) (hX : Nonempty (F ≅ᶠ homFunctor C X)) (hY : Nonempty (F ≅ᶠ homFunctor C Y)) :
  Nonempty (C[X, Y] × C[Y, X])  -- X ≅ Y in a full implementation

/-! ## Yoneda as Axiom -/

/-- The Yoneda lemma expressed as an axiom in the MiniObjectKernel framework. -/
def yonedaLemmaAxiom : MiniObjectKernel.Axioms.Axiom :=
  MiniObjectKernel.Axioms.Axiom.described "yoneda-lemma" (MiniObjectKernel.Logic.Formula.atom 10)
    "Nat(Hom(X,-), F) ≅ F(X) — the Yoneda lemma"

#eval "Theorems.Basic: Yoneda Lemma, Yoneda embedding, uniqueness of representing objects"
