import MiniCategoryCore

open MiniCategoryCore

-- Benchmark targets for mini-category-core (MIT)
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniCategoryCore/Core/Basic.lean:23", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:57", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:73", "DONE"),
  ("MiniCategoryCore/Core/Objects.lean:28", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:19", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:47", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:10", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:17", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:24", "DONE"),
  ("MiniCategoryCore/Constructions/Products.lean:14", "DONE"),
  ("MiniCategoryCore/Properties/Preservation.lean:14", "DONE"),
  ("MiniCategoryCore/Properties/ClassificationData.lean:20", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "STUB" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"MIT: {done}/{total} done ({pct}%), {stub} stubs"
