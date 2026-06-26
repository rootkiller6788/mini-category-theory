import MiniCategoryCore

open MiniCategoryCore

-- Benchmark targets for mini-category-core (Cambridge Part III)
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniCategoryCore/Core/Basic.lean:23", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:73", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:90", "DONE"),
  ("MiniCategoryCore/Core/Objects.lean:28", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:32", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:42", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:47", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:17", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:24", "DONE"),
  ("MiniCategoryCore/Morphisms/Equivalence.lean:10", "DONE"),
  ("MiniCategoryCore/Constructions/Subobjects.lean:12", "DONE"),
  ("MiniCategoryCore/Constructions/Quotients.lean:12", "DONE")
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
