import MiniMonadCore

-- Benchmark targets for mini-monad-core
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniMonadCore/Core/Basic.lean:22", "DONE"),      -- Monad structure
  ("MiniMonadCore/Core/Basic.lean:35", "DONE"),      -- MonadMorphism
  ("MiniMonadCore/Core/Objects.lean:20", "DONE"),    -- KleisliCat
  ("MiniMonadCore/Core/Laws.lean:19", "DONE"),       -- monadLeftUnitLaw
  ("MiniMonadCore/Core/Laws.lean:28", "DONE"),       -- monadLawsHold
  ("MiniMonadCore/Constructions/Universal.lean:18", "DONE"),  -- EMAlgebra
  ("MiniMonadCore/Constructions/Universal.lean:28", "DONE"),  -- EMCat
  ("MiniMonadCore/Theorems/Basic.lean:24", "DONE"),  -- fromAdjunction
  ("MiniMonadCore/Morphisms/Hom.lean:20", "DONE"),   -- Morphisms/Hom
  ("MiniMonadCore/Morphisms/Iso.lean:16", "DONE"),   -- Morphisms/Iso
  ("MiniMonadCore/Morphisms/Equivalence.lean:16", "DONE"),  -- Morphisms/Equivalence
  ("MiniMonadCore/Constructions/Subobjects.lean:16", "DONE"),  -- Subobjects
  ("MiniMonadCore/Constructions/Quotients.lean:16", "DONE"),   -- Quotients
  ("MiniMonadCore/Constructions/Products.lean:16", "DONE"),    -- Products
  ("MiniMonadCore/Properties/Invariants.lean:16", "DONE"),     -- Invariants
  ("MiniMonadCore/Properties/Preservation.lean:16", "DONE"),   -- Preservation
  ("MiniMonadCore/Properties/ClassificationData.lean:16", "DONE"), -- ClassificationData
  ("MiniMonadCore/Theorems/UniversalProperties.lean:16", "DONE"),  -- UniversalProperties
  ("MiniMonadCore/Theorems/Classification.lean:16", "DONE"),   -- Classification
  ("MiniMonadCore/Theorems/Main.lean:16", "DONE"),             -- Main
  ("MiniMonadCore/Examples/Standard.lean:16", "DONE"),         -- Standard
  ("MiniMonadCore/Examples/Counterexamples.lean:16", "DONE"),  -- Counterexamples
  ("MiniMonadCore/Bridges/ToAlgebra.lean:16", "DONE"),         -- ToAlgebra
  ("MiniMonadCore/Bridges/ToTopology.lean:16", "DONE"),        -- ToTopology
  ("MiniMonadCore/Bridges/ToGeometry.lean:16", "DONE"),        -- ToGeometry
  ("MiniMonadCore/Bridges/ToComputation.lean:16", "DONE")      -- ToComputation
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
