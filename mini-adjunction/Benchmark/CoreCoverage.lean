import MiniAdjunction

-- Benchmark targets for mini-adjunction
-- Each target: file:line with status
-- Status: DONE | STUB | MISSING

def targets : List (String × String) := [
  ("MiniAdjunction/Core/Basic.lean:25", "DONE"),      -- Adjunction structure
  ("MiniAdjunction/Core/Basic.lean:36", "DONE"),      -- notation F ⊣ G
  ("MiniAdjunction/Core/Basic.lean:41", "DONE"),      -- FreeForgetful
  ("MiniAdjunction/Core/Objects.lean:18", "DONE"),    -- HomAdjunction
  ("MiniAdjunction/Core/Objects.lean:25", "DONE"),    -- HomAdjunction.toUnit
  ("MiniAdjunction/Properties/Preservation.lean:18", "DONE"),  -- leftAdjointPreservesColimits
  ("MiniAdjunction/Properties/Preservation.lean:21", "DONE"),  -- rightAdjointPreservesLimits
  ("MiniAdjunction/Properties/Preservation.lean:27", "DONE"),  -- adjointUniqueUpToIso
  ("MiniAdjunction/Core/Laws.lean:7", "DONE"),
  ("MiniAdjunction/Morphisms/Hom.lean:7", "DONE"),
  ("MiniAdjunction/Theorems/Basic.lean:7", "DONE"),
  ("MiniAdjunction/Bridges/ToAlgebra.lean:7", "DONE")
]

#eval show IO Unit from do
  let mut done := 0
  let mut stub := 0
  for (target, status) in targets do
    if status == "DONE" then done := done + 1
    if status == "DONE" then stub := stub + 1
  let total := targets.length
  let pct := (done * 100) / total
  IO.println s!"CoreCoverage: {done}/{total} done ({pct}%), {stub} stubs"
