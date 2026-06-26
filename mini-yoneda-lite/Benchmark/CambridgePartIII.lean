import MiniYonedaLite

-- Cambridge Part III benchmark targets for mini-yoneda-lite
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniYonedaLite/Core/Basic.lean:35", "DONE"),
  ("MiniYonedaLite/Core/Basic.lean:40", "DONE"),
  ("MiniYonedaLite/Core/Basic.lean:50", "DONE"),
  ("MiniYonedaLite/Core/Objects.lean:20", "DONE"),
  ("MiniYonedaLite/Core/Laws.lean:30", "DONE"),
  ("MiniYonedaLite/Morphisms/Hom.lean:20", "DONE"),
  ("MiniYonedaLite/Morphisms/Iso.lean:20", "DONE"),
  ("MiniYonedaLite/Theorems/Basic.lean:43", "DONE"),
  ("MiniYonedaLite/Theorems/Basic.lean:53", "DONE"),
  ("MiniYonedaLite/Theorems/Main.lean:43", "DONE"),
  ("MiniYonedaLite/Theorems/UniversalProperties.lean:20", "DONE"),
  ("MiniYonedaLite/Theorems/Classification.lean:20", "DONE"),
  ("MiniYonedaLite/Examples/Standard.lean:40", "DONE"),
  ("MiniYonedaLite/Examples/Counterexamples.lean:20", "DONE"),
  ("MiniYonedaLite/Bridges/ToAlgebra.lean:20", "DONE"),
  ("MiniYonedaLite/Bridges/ToTopology.lean:20", "DONE"),
  ("MiniYonedaLite/Bridges/ToGeometry.lean:20", "DONE"),
  ("MiniYonedaLite/Bridges/ToComputation.lean:20", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "STUB" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"CambridgePartIII: {done}/{total} done ({pct}%), {stub} stubs"
