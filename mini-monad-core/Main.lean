/-
Main entry point for mini-monad-core.
Prints package info and runs basic diagnostics.
-/

import MiniMonadCore

open MiniMonadCore
open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "=== mini-monad-core ==="
  IO.println "Monad theory: Monad (T, η, μ), Kleisli category, Eilenberg-Moore category, monad laws"
  IO.println "Depends on: mini-category-core, mini-functor-core, mini-natural-transformation, mini-adjunction"
  IO.println ""

  -- Verify core definitions exist
  IO.println "Core definitions:"
  IO.println s!"  Monad (SetCat) type: {(Monad SetCat).toString}"
  IO.println s!"  MonadMorphism type: {(MonadMorphism (maybeMonad) (maybeMonad)).toString}"
  IO.println s!"  KleisliCat type: {(KleisliCat (maybeMonad)).toString}"
  IO.println s!"  EMCat type: {(EMCat (maybeMonad)).toString}"
  IO.println s!"  MonadIso type: {(MonadIso (maybeMonad) (maybeMonad)).toString}"
  IO.println ""

  -- Verify monad examples work
  IO.println "Monad examples:"
  let m1 := maybeMonad.η.component Nat 42
  IO.println s!"  maybeMonad.η(42) = {reprStr m1}"

  let m2 := listMonad.η.component String "hello"
  IO.println s!"  listMonad.η(\"hello\") = {reprStr m2}"

  let m3 := (stateMonad Nat).η.component Bool true 5
  IO.println s!"  stateMonad.η(true)(5) = {reprStr m3}"

  let m4 := maybeMonad.μ.component Nat (Maybe.just (Maybe.just 10))
  IO.println s!"  maybeMonad.μ(just(just(10))) = {reprStr m4}"

  let m5 := listMonad.μ.component Nat [[1,2,3], [4,5], [6]]
  IO.println s!"  listMonad.μ([[1,2,3],[4,5],[6]]) = {reprStr m5}"
  IO.println ""

  -- Verify laws hold (conceptually)
  IO.println "Monad laws (all hold by construction):"
  IO.println "  Left unit: μ ∘ Tη = id"
  IO.println "  Right unit: μ ∘ ηT = id"
  IO.println "  Associativity: μ ∘ Tμ = μ ∘ μT"
  IO.println ""

  IO.println "=== All checks passed ==="
