/-
# MiniFunctorCore.Core.Objects

Object instance registrations for Functor-related types.
Registers functor-theoretic types with the kernel's `Object` typeclass.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Theory Names -/

def functorTheory : MiniObjectKernel.Objects.TheoryName :=
  MiniObjectKernel.Objects.TheoryName.ofString "FunctorTheory"

def functorTheoryCore : MiniObjectKernel.Objects.TheoryName :=
  functorTheory.extend "Core"
def functorTheoryCategories : MiniObjectKernel.Objects.TheoryName :=
  functorTheory.extend "FunctorCategories"
def functorTheoryPresheaves : MiniObjectKernel.Objects.TheoryName :=
  functorTheory.extend "Presheaves"
def functorTheoryDiagrams : MiniObjectKernel.Objects.TheoryName :=
  functorTheory.extend "Diagrams"

/-! ## Object Instances -/

instance : MiniObjectKernel.Objects.Object (Functor C D) where
  theory := catTheoryFunctors
  objName := "Functor"
  repr _ := "F"

instance : MiniObjectKernel.Objects.Object (SliceObj C X) where
  theory := functorTheoryDiagrams
  objName := "SliceObj"
  repr _ := "S/X"

instance : MiniObjectKernel.Objects.Object (CosliceObj C X) where
  theory := functorTheoryDiagrams
  objName := "CosliceObj"
  repr _ := "X/S"

instance : MiniObjectKernel.Objects.Object (TwistedArrow C) where
  theory := functorTheoryDiagrams
  objName := "TwistedArrow"
  repr _ := "Tw(f)"

/-! ## Functor Category Size Tags -/

inductive FunctorSize where
  | small
  | locallySmall
  | large
  deriving Repr, DecidableEq

structure SizedFunctorCategory (C D : Category) where
  cat : Category
  size : FunctorSize

/-! ## Theory Registration -/

def functorTheoryNode : MiniObjectKernel.Dependency.TheoryNode :=
  MiniObjectKernel.Dependency.TheoryNode.simple catTheoryFunctors
    "Functor Theory" "0.1.0" "2. mini-category-theory"

def functorDependencyEdges : List MiniObjectKernel.Dependency.Edge := [
  { from := functorTheory, to := MiniObjectKernel.Objects.TheoryName.ofString "MiniMathKernel", label := "imports" },
  { from := functorTheory, to := catTheory, label := "extends" }
]

#eval "Core.Objects: FunctorTheory theory, Functor, SliceObj, CosliceObj, TwistedArrow Object instances registered"
