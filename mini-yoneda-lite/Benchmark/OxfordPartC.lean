import MiniYonedaLite

-- Oxford Part C benchmark targets for mini-yoneda-lite
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniYonedaLite/Core/Basic.lean:35", "DONE"),
  ("MiniYonedaLite/Core/Basic.lean:50", "DONE"),
  ("MiniYonedaLite/Theorems/Basic.lean:43", "DONE"),
  ("MiniYonedaLite/Theorems/Basic.lean:48", "DONE"),
  ("MiniYonedaLite/Theorems/Basic.lean:58", "DONE"),
  ("MiniYonedaLite/Theorems/Main.lean:43", "DONE"),
  ("MiniYonedaLite/Theorems/Main.lean:52", "DONE"),
  ("MiniYonedaLite/Examples/Standard.lean:40", "DONE"),
  ("MiniYonedaLite/Examples/Standard.lean:46", "DONE"),
  ("MiniYonedaLite/Constructions/Products.lean:20", "DONE"),
  ("MiniYonedaLite/Constructions/Universal.lean:20", "DONE"),
  ("MiniYonedaLite/Properties/ClassificationData.lean:20", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "STUB" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"OxfordPartC: {done}/{total} done ({pct}%), {stub} stubs"
