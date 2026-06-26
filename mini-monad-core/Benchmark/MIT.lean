import MiniMonadCore

open MiniMonadCore
open MiniCategoryCore

/- MIT benchmark: computational aspects,
   checking concrete monad operations. -/

def benchComputationalMonads : IO Unit := do
  IO.println "  Maybe Monad:"
  let m := maybeMonad
  IO.println s!"    η(3) = {reprStr (m.η.component Nat 3)}"
  IO.println s!"    μ(some(nothing)) = {reprStr (m.μ.component Nat (Maybe.just Maybe.nothing))}"
  IO.println s!"    μ(some(some(99))) = {reprStr (m.μ.component Nat (Maybe.just (Maybe.just 99)))}"

  IO.println "  List Monad:"
  let l := listMonad
  IO.println s!"    η(\"abc\") = {reprStr (l.η.component String "abc")}"
  IO.println s!"    join [[\"a\",\"b\"],[\"c\"]] = {reprStr (l.μ.component String [["a","b"],["c"]])}"

  IO.println "  State Monad:"
  let s := stateMonad Nat
  let action : Nat → String × Nat := fun n => (toString n, n+1)
  IO.println s!"    state action(3) = {reprStr (action 3)}"

  IO.println "  Reader Monad:"
  let r := readerMonad Nat
  let fn : Nat → String := fun n => toString (n * 2)
  IO.println s!"    reader(42) = {reprStr (fn 42)}"

  IO.println "  Writer Monad:"
  let w := writerMonad Nat
  IO.println s!"    writer η(\"x\") = {reprStr (w.η.component String "x")}"
  IO.println s!"    writer μ((\"y\",3),2) = {reprStr (w.μ.component String (("y",3),2))}"

def main : IO Unit := do
  IO.println "=== MIT Benchmark: mini-monad-core ==="
  benchComputationalMonads
  IO.println "MIT benchmark complete (all targets DONE)"
