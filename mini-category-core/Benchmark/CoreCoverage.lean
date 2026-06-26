import MiniCategoryCore

open MiniCategoryCore

-- Benchmark targets for mini-category-core
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  -- Core/Basic.lean (foundational)
  ("MiniCategoryCore/Core/Basic.lean:23", "DONE"),     -- Category structure
  ("MiniCategoryCore/Core/Basic.lean:45", "DONE"),     -- SetCat
  ("MiniCategoryCore/Core/Basic.lean:57", "DONE"),     -- Cᵒᵖ
  ("MiniCategoryCore/Core/Basic.lean:73", "DONE"),     -- C×ᶜD
  ("MiniCategoryCore/Core/Basic.lean:90", "DONE"),     -- DiscCat
  ("MiniCategoryCore/Core/Basic.lean:111", "DONE"),    -- CodiscCat  -- Core/Objects.lean
  ("MiniCategoryCore/Core/Objects.lean:28", "DONE"),   -- Object instance
  ("MiniCategoryCore/Core/Objects.lean:62", "DONE"),   -- Iso structure
  ("MiniCategoryCore/Core/Objects.lean:70", "DONE"),   -- iso_refl
  ("MiniCategoryCore/Core/Objects.lean:76", "DONE"),   -- iso_symm
  ("MiniCategoryCore/Core/Objects.lean:81", "DONE"),   -- iso_trans
  -- Core/Laws.lean
  ("MiniCategoryCore/Core/Laws.lean:19", "DONE"),      -- associativityLaw
  ("MiniCategoryCore/Core/Laws.lean:32", "DONE"),      -- categoryLaws theorem
  ("MiniCategoryCore/Core/Laws.lean:42", "DONE"),      -- preservesId
  ("MiniCategoryCore/Core/Laws.lean:47", "DONE"),      -- preservesComp
  ("MiniCategoryCore/Core/Laws.lean:92", "DONE"),      -- iso_is_equiv_rel
  ("MiniCategoryCore/Core/Laws.lean:99", "DONE"),      -- id_is_iso
  ("MiniCategoryCore/Core/Laws.lean:107", "DONE"),     -- comp_iso
  -- Morphisms
  ("MiniCategoryCore/Morphisms/Hom.lean:12", "DONE"),  -- Mono/Epi
  ("MiniCategoryCore/Morphisms/Hom.lean:38", "DONE"),  -- SplitMono/SplitEpi
  ("MiniCategoryCore/Morphisms/Hom.lean:97", "DONE"),  -- isIso_iff_split_mono_epi
  ("MiniCategoryCore/Morphisms/Iso.lean:12", "DONE"),  -- whisker
  ("MiniCategoryCore/Morphisms/Iso.lean:65", "DONE"),  -- IsoNatSquare
  ("MiniCategoryCore/Morphisms/Equivalence.lean:10", "DONE"), -- Functor
  ("MiniCategoryCore/Morphisms/Equivalence.lean:40", "DONE"), -- Equivalence
  -- Constructions
  ("MiniCategoryCore/Constructions/Universal.lean:10", "DONE"),  -- Initial
  ("MiniCategoryCore/Constructions/Universal.lean:17", "DONE"),  -- Terminal
  ("MiniCategoryCore/Constructions/Universal.lean:24", "DONE"),  -- Zero
  ("MiniCategoryCore/Constructions/Products.lean:14", "DONE"),   -- ProductCone
  ("MiniCategoryCore/Constructions/Products.lean:47", "DONE"),   -- SetCat product
  ("MiniCategoryCore/Constructions/Subobjects.lean:12", "DONE"), -- Subobject
  ("MiniCategoryCore/Constructions/Quotients.lean:14", "DONE"),  -- CatCongruence
  -- Properties
  ("MiniCategoryCore/Properties/Invariants.lean:10", "DONE"),     -- isSkeletal
  ("MiniCategoryCore/Properties/Invariants.lean:26", "DONE"),     -- isGaunt
  ("MiniCategoryCore/Properties/Invariants.lean:62", "DONE"),     -- isGroupoid
  ("MiniCategoryCore/Properties/Invariants.lean:78", "DONE"),     -- isConnected
  ("MiniCategoryCore/Properties/Preservation.lean:14", "DONE"),   -- terminal preserved
  ("MiniCategoryCore/Properties/ClassificationData.lean:20", "DONE"), -- PreorderCat
  ("MiniCategoryCore/Properties/ClassificationData.lean:45", "DONE"), -- MonoidCat
  -- Theorems
  ("MiniCategoryCore/Theorems/Basic.lean:14", "DONE"),    -- terminal_unique
  ("MiniCategoryCore/Theorems/Basic.lean:26", "DONE"),    -- initial_unique
  ("MiniCategoryCore/Theorems/Basic.lean:42", "DONE"),    -- mono+epi=iso in SetCat
  ("MiniCategoryCore/Theorems/UniversalProperties.lean:12", "DONE"), -- terminal as limit
  ("MiniCategoryCore/Theorems/Classification.lean:18", "DONE"),     -- skeleton theorem
  ("MiniCategoryCore/Theorems/Main.lean:18", "DONE"),      -- Yoneda
  ("MiniCategoryCore/Theorems/Main.lean:28", "DONE"),      -- Adjoint functor theorem
  -- Examples
  ("MiniCategoryCore/Examples/Standard.lean:12", "DONE"),  -- SetCat example
  ("MiniCategoryCore/Examples/Counterexamples.lean:12", "DONE"), -- mono+epi not iso
  -- Bridges
  ("MiniCategoryCore/Bridges/ToAlgebra.lean:12", "DONE"),     -- monoid as cat
  ("MiniCategoryCore/Bridges/ToTopology.lean:12", "DONE"),    -- TopCategory
  ("MiniCategoryCore/Bridges/ToGeometry.lean:12", "DONE"),    -- ManifoldCat
  ("MiniCategoryCore/Bridges/ToComputation.lean:12", "DONE")  -- C.C.C.
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
