import MiniLimitColimit

-- Benchmark targets for mini-limit-colimit
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniLimitColimit/Core/Basic.lean", "DONE"),
  ("MiniLimitColimit/Core/Objects.lean", "DONE"),
  ("MiniLimitColimit/Core/Laws.lean", "DONE"),
  ("MiniLimitColimit/Morphisms/Hom.lean", "DONE"),
  ("MiniLimitColimit/Morphisms/Iso.lean", "DONE"),
  ("MiniLimitColimit/Morphisms/Equivalence.lean", "DONE"),
  ("MiniLimitColimit/Constructions/Products.lean", "DONE"),
  ("MiniLimitColimit/Constructions/Universal.lean", "DONE"),
  ("MiniLimitColimit/Constructions/Subobjects.lean", "DONE"),
  ("MiniLimitColimit/Constructions/Quotients.lean", "DONE"),
  ("MiniLimitColimit/Properties/Invariants.lean", "DONE"),
  ("MiniLimitColimit/Properties/Preservation.lean", "DONE"),
  ("MiniLimitColimit/Properties/ClassificationData.lean", "DONE"),
  ("MiniLimitColimit/Theorems/Basic.lean", "DONE"),
  ("MiniLimitColimit/Theorems/UniversalProperties.lean", "DONE"),
  ("MiniLimitColimit/Theorems/Classification.lean", "DONE"),
  ("MiniLimitColimit/Theorems/Main.lean", "DONE"),
  ("MiniLimitColimit/Examples/Standard.lean", "DONE"),
  ("MiniLimitColimit/Examples/Counterexamples.lean", "DONE"),
  ("MiniLimitColimit/Bridges/ToAlgebra.lean", "DONE"),
  ("MiniLimitColimit/Bridges/ToTopology.lean", "DONE"),
  ("MiniLimitColimit/Bridges/ToGeometry.lean", "DONE"),
  ("MiniLimitColimit/Bridges/ToComputation.lean", "DONE")
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
