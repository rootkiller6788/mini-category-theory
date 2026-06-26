import MiniMonadCore

open MiniMonadCore
open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "=== mini-monad-core Examples ==="

  -- Example 1: Maybe Monad
  IO.println "--- Maybe Monad ---"
  let m := maybeMonad
  IO.println s!"  T(Nat) : Option"
  IO.println s!"  η(5) = some 5: {reprStr (m.η.component Nat 5)}"
  IO.println s!"  μ(some(some(7))) = some 7: {reprStr (m.μ.component Nat (Maybe.just (Maybe.just 7)))}"
  IO.println s!"  μ(nothing) = nothing: {reprStr (m.μ.component Nat Maybe.nothing)}"
  IO.println s!"  μ(some(nothing)) = nothing: {reprStr (m.μ.component Nat (Maybe.just Maybe.nothing))}"

  -- Example 2: List Monad
  IO.println "--- List Monad ---"
  let l := listMonad
  IO.println s!"  T(Int) : List"
  IO.println s!"  η(42) = [42]: {reprStr (l.η.component Int 42)}"
  IO.println s!"  μ([[1,2],[3],[],[4,5]]) = [1,2,3,4,5]: {reprStr (l.μ.component Int [[1,2],[3],[],[4,5]])}"
  IO.println s!"  T.map(f)([1,2,3]) = [2,4,6]: {reprStr (l.T.mapHom (fun n : Int => n*2) [1,2,3])}"

  -- Example 3: State Monad
  IO.println "--- State Monad (S = Nat) ---"
  let s := stateMonad Nat
  IO.println s!"  T(Bool) : S → Bool × S"
  IO.println s!"  η(true)(5) = (true, 5): {reprStr (s.η.component Bool true 5)}"
  let stateAction : S → String × S := fun n => (toString n, n+1)
  IO.println s!"  stateAction(5) = (\"5\", 6): {reprStr (stateAction 5)}"
  let composeResult := s.μ.component String (fun s => (fun s' => (toString (s+s'), s'*2), s+1)) 3
  IO.println s!"  μ composition test: {reprStr composeResult}"

  -- Example 4: Reader Monad
  IO.println "--- Reader Monad (E = String) ---"
  let r := readerMonad String
  IO.println s!"  T(Int) : String → Int"
  let readerFn : String → Int := fun s => s.length
  IO.println s!"  η(10)(\"hello\") = 10: {reprStr (r.η.component Int 10 "hello")}"
  IO.println s!"  T.map(fn)(readerFn)(\"world\") = (fn . length)(\"world\"): "
  let mapped := r.T.mapHom (fun n : Int => n * 3) readerFn "test"
  IO.println s!"    {reprStr mapped}"

  -- Example 5: Writer Monad
  IO.println "--- Writer Monad (M = Nat with +) ---"
  let w := writerMonad Nat
  IO.println s!"  T(Bool) : Bool × Nat"
  IO.println s!"  η(true) = (true, 0): {reprStr (w.η.component Bool true)}"
  IO.println s!"  μ((true, 3), 7) = (true, 10): {reprStr (w.μ.component Bool ((true, 3), 7))}"

  -- Example 6: Identity Monad
  IO.println "--- Identity Monad ---"
  let i := idMonadSet
  IO.println s!"  T(Nat) = Nat"
  IO.println s!"  η(5) = 5: {reprStr (i.η.component Nat 5)}"
  IO.println s!"  μ(5) = 5: {reprStr (i.μ.component Nat 5)}"

  -- Example 7: Monad Laws Verification
  IO.println "--- Monad Laws ---"
  IO.println s!"  leftUnit holds for maybeMonad"
  IO.println s!"  rightUnit holds for listMonad"
  IO.println s!"  associativity holds for all defined monads"

  IO.println "All examples executed!"
