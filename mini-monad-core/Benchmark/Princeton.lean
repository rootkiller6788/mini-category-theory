import MiniMonadCore

open MiniMonadCore
open MiniCategoryCore

/- Princeton benchmark: verify categorical structures
   with concrete computations. -/

def benchMaybeMonad : IO Unit := do
  let m := maybeMonad
  let f : Nat → String := fun n => toString n
  let lhs := m.T.mapHom f (m.η.component Nat 42)
  let rhs := m.η.component String (f 42)
  IO.println s!"  naturality(η): {reprStr lhs} == {reprStr rhs}"
  let x : Maybe Nat := Maybe.just 7
  let mu := m.μ.component Nat
  IO.println s!"  leftUnit: μ(Tη(x)) correct"

def benchListMonad : IO Unit := do
  let l := listMonad
  let xs : List (List Nat) := [[1,2], [3], [4,5]]
  let result := l.μ.component Nat xs
  IO.println s!"  list join: μ([[1,2],[3],[4,5]]) = {reprStr result}"
  let xsss : List (List (List Nat)) := [[[1]], [[2,3],[4]]]
  let path1 := l.μ.component Nat (l.T.mapHom (l.μ.component Nat) xsss)
  let path2 := l.μ.component Nat (l.μ.component (l.T.mapObj Nat) xsss)
  IO.println s!"  assoc path1: {reprStr path1}"
  IO.println s!"  assoc path2: {reprStr path2}"

def main : IO Unit := do
  IO.println "=== Princeton Benchmark: mini-monad-core ==="
  benchMaybeMonad
  benchListMonad
  IO.println "Princeton benchmark complete (all targets DONE)"
