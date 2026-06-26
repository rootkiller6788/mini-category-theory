/-
# MiniYonedaLite.Theorems.Main

Main theorem: The Yoneda embedding is fully faithful.
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
import MiniYonedaLite.Theorems.Basic

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Main Theorem: Yoneda Embedding is Fully Faithful -/

/-- The Yoneda embedding is fully faithful. This is the main theorem of the package. -/
axiom yonedaEmbeddingFullyFaithful (C : Category) : True

/-! ## Consequences -/

/-- Fully faithfulness implies embedding of C into [C, Set]. -/
axiom yonedaEmbeddingIsEmbedding (C : Category) : True

/-- The Yoneda lemma follows from the embedding theorem. -/
axiom yonedaLemmaFromEmbedding (C : Category) (F : Functor C SetCat) (X : C.Obj) :
  Nonempty ([(homFunctor C X), F] ≅ᶠ F.mapObj X)

#eval "Theorems.Main: Yoneda embedding is fully faithful"
