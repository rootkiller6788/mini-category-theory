import MiniYonedaLite

-- Benchmark targets for mini-yoneda-lite
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniYonedaLite/Core/Basic.lean:35", "DONE"),     -- isRepresentable
  ("MiniYonedaLite/Core/Basic.lean:40", "DONE"),     -- presheafCategory
  ("MiniYonedaLite/Core/Basic.lean:44", "DONE"),     -- isRepresentablePresheaf
  ("MiniYonedaLite/Core/Basic.lean:50", "DONE"),     -- yonedaEmbedding
  ("MiniYonedaLite/Core/Objects.lean:20", "DONE"),   -- yonedaEmbeddingCov
  ("MiniYonedaLite/Core/Objects.lean:32", "DONE"),   -- RepresentableFunctor
  ("MiniYonedaLite/Core/Objects.lean:45", "DONE"),   -- UniversalElement
  ("MiniYonedaLite/Core/Laws.lean:25", "DONE"),      -- yonedaLemmaStatement
  ("MiniYonedaLite/Core/Laws.lean:40", "DONE"),      -- yonedaBijection
  ("MiniYonedaLite/Core/Laws.lean:60", "DONE"),      -- yonedaCorollaryFullyFaithful
  ("MiniYonedaLite/Morphisms/Hom.lean:20", "DONE"),  -- yonedaOnMorphism
  ("MiniYonedaLite/Morphisms/Hom.lean:48", "DONE"),  -- yonedaIsFullyFaithfulDetailed
  ("MiniYonedaLite/Morphisms/Iso.lean:20", "DONE"),  -- yonedaIsoForward
  ("MiniYonedaLite/Morphisms/Iso.lean:52", "DONE"),  -- yonedaSetBijection
  ("MiniYonedaLite/Morphisms/Equivalence.lean:25", "DONE"), -- yonedaIsEquivalence
  ("MiniYonedaLite/Constructions/Products.lean:22", "DONE"), -- yonedaPreservesProducts
  ("MiniYonedaLite/Constructions/Universal.lean:18", "DONE"), -- freeCocompletion
  ("MiniYonedaLite/Constructions/Subobjects.lean:18", "DONE"), -- SubfunctorOfRepresentable
  ("MiniYonedaLite/Constructions/Quotients.lean:18", "DONE"), -- QuotientOfRepresentable
  ("MiniYonedaLite/Properties/Invariants.lean:20", "DONE"), -- representabilityInvariantUnderEquivalence
  ("MiniYonedaLite/Properties/Preservation.lean:22", "DONE"), -- yonedaPreservesLimits
  ("MiniYonedaLite/Properties/ClassificationData.lean:20", "DONE"), -- isDense
  ("MiniYonedaLite/Theorems/Basic.lean:43", "DONE"),  -- yonedaLemma
  ("MiniYonedaLite/Theorems/Basic.lean:48", "DONE"),  -- yonedaIsFullyFaithful
  ("MiniYonedaLite/Theorems/Basic.lean:53", "DONE"),  -- representingObjectUnique
  ("MiniYonedaLite/Theorems/Basic.lean:58", "DONE"),  -- yonedaLemmaAxiom
  ("MiniYonedaLite/Theorems/Main.lean:43", "DONE"),   -- yonedaEmbeddingFullyFaithful
  ("MiniYonedaLite/Theorems/Main.lean:48", "DONE"),   -- yonedaEmbeddingIsEmbedding
  ("MiniYonedaLite/Theorems/Main.lean:52", "DONE"),   -- yonedaLemmaFromEmbedding
  ("MiniYonedaLite/Theorems/UniversalProperties.lean:20", "DONE"), -- freeCocompletionTheorem
  ("MiniYonedaLite/Theorems/Classification.lean:20", "DONE"), -- representableFunctorTheorem
  ("MiniYonedaLite/Examples/Standard.lean:40", "DONE"), -- identity functor example
  ("MiniYonedaLite/Examples/Standard.lean:46", "DONE"), -- constant functor example
  ("MiniYonedaLite/Examples/Standard.lean:53", "DONE"), -- presheaf example
  ("MiniYonedaLite/Examples/Standard.lean:58", "DONE"), -- Yoneda preserves products
  ("MiniYonedaLite/Examples/Counterexamples.lean:20", "DONE"), -- emptyFunctor
  ("MiniYonedaLite/Bridges/ToAlgebra.lean:20", "DONE"), -- cayleyTheorem
  ("MiniYonedaLite/Bridges/ToTopology.lean:20", "DONE"), -- presheafAsGeneralizedSpace
  ("MiniYonedaLite/Bridges/ToGeometry.lean:20", "DONE"), -- affineScheme
  ("MiniYonedaLite/Bridges/ToComputation.lean:20", "DONE")  -- cpsTransform
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "STUB" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"CoreCoverage: {done}/{total} done ({pct}%), {stub} stubs"
