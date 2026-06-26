import MiniAdjunction

-- Benchmark targets for mini-adjunction
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniAdjunction/Core/Basic.lean:25", "DONE"),
  ("MiniAdjunction/Core/Basic.lean:41", "DONE"),
  ("MiniAdjunction/Core/Objects.lean:18", "DONE"),
  ("MiniAdjunction/Core/Objects.lean:25", "DONE"),
  ("MiniAdjunction/Properties/Preservation.lean:21", "DONE"),
  ("MiniAdjunction/Properties/Preservation.lean:27", "DONE"),
  ("MiniAdjunction/Core/Laws.lean:7", "DONE"),
  ("MiniAdjunction/Morphisms/Equivalence.lean:7", "DONE"),
  ("MiniAdjunction/Constructions/Subobjects.lean:7", "DONE"),
  ("MiniAdjunction/Constructions/Quotients.lean:7", "DONE"),
  ("MiniAdjunction/Theorems/Classification.lean:7", "DONE"),
  ("MiniAdjunction/Examples/Counterexamples.lean:7", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "DONE" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"CambridgePartIII: {done}/{total} done ({pct}%), {stub} stubs"
