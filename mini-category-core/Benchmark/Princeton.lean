import MiniCategoryCore

open MiniCategoryCore

-- Benchmark targets for mini-category-core (Princeton)
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniCategoryCore/Core/Basic.lean:23", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:45", "DONE"),
  ("MiniCategoryCore/Core/Basic.lean:57", "DONE"),
  ("MiniCategoryCore/Core/Objects.lean:28", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:19", "DONE"),
  ("MiniCategoryCore/Core/Laws.lean:32", "DONE"),
  ("MiniCategoryCore/Constructions/Universal.lean:10", "DONE"),
  ("MiniCategoryCore/Morphisms/Hom.lean:12", "DONE"),
  ("MiniCategoryCore/Morphisms/Iso.lean:12", "DONE"),
  ("MiniCategoryCore/Constructions/Products.lean:14", "DONE"),
  ("MiniCategoryCore/Bridges/ToAlgebra.lean:12", "DONE"),
  ("MiniCategoryCore/Bridges/ToTopology.lean:12", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "STUB" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"Princeton: {done}/{total} done ({pct}%), {stub} stubs"
