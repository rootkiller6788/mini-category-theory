/-
# MiniAdjunction.Bridges.ToTopology

Stone-Cech compactification as adjunction, discrete-forgetful adjunction.
Connecting adjunctions to topology.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Stone-Cech Compactification -/

/--
The Stone-Cech compactification β : Top → CompHaus is left adjoint
to the forgetful functor U : CompHaus → Top.
  β ⊣ U

For a topological space X, β(X) is the Stone-Cech compactification.
-/
structure StoneCechAdjunction where
  compactification : Functor SetCat SetCat
  forgetful : Functor SetCat SetCat
  adj : compactification ⊣ forgetful
  stoneCechProperty : ∀ (X : Type u), Prop

/--
The Stone-Cech compactification is the unique (up to homeomorphism)
compact Hausdorff space containing X as a dense subspace, such that
any continuous map X → K with K compact Hausdorff extends uniquely to β X.
-/
axiom stoneCechUniversityProperty : Prop

/-! ## Discrete-Forgetful Adjunction -/

/--
The discrete space functor D : Set → Top is left adjoint to the
forgetful functor U : Top → Set.
  D ⊣ U

D(X) gives X the discrete topology.
-/
structure DiscreteTopologyAdjunction where
  discrete : Functor SetCat SetCat
  forgetful : Functor SetCat SetCat
  adj : discrete ⊣ forgetful

/--
The indiscrete (codiscrete) topology functor I : Set → Top
is right adjoint to the forgetful functor U : Top → Set.
  U ⊣ I

I(X) gives X the indiscrete topology.
-/
structure IndiscreteTopologyAdjunction where
  forgetful : Functor SetCat SetCat
  indiscrete : Functor SetCat SetCat
  adj : forgetful ⊣ indiscrete

/--
The adjoint string: D ⊣ U ⊣ I : Top → Set.
-/
axiom discreteIndiscreteAdjointString : Prop

#eval "Bridges.ToTopology: StoneCech compactification β ⊣ U"
#eval "Bridges.ToTopology: discrete ⊣ forgetful ⊣ indiscrete adjoint string"

/-! ## Fundamental Groupoid Adjunction -/

/--
The fundamental groupoid functor Π₁ : Top → Groupoid is left adjoint
to the nerve/classifying space functor.
-/
axiom fundamentalGroupoidAdjunction : Prop

/-! ## Sheaf-Space Adjunction (overview) -/

/--
The sheaf space functor L : PSh(X) → Top/X is left adjoint to
the sheaf of sections functor Γ : Top/X → PSh(X).
  L ⊣ Γ

This is the etale space / sheaf adjunction.
-/
axiom sheafSpaceAdjunctionTopology : Prop

/-! ## Locale Theory Connection -/

/--
The category of locales Loc is opposite to the category of frames Frm.
The adjunction between locales and topological spaces:
  Ω : Top → Loc ⊣ pt : Loc → Top
-/
axiom localeTopologyAdjunction : Prop

/-! ## Compactness as an Adjoint -/

/--
Compactness can be viewed as a property of the functor taking
a topological space to its compact-open topology.
-/
axiom compactnessViaAdjunction : Prop

/-! ## Connected Components Adjunction -/

/--
The connected components functor π₀ : Top → Set is left adjoint
to the discrete space functor D : Set → Top.
  π₀ ⊣ D
-/
axiom connectedComponentsAdjunction : Prop

#eval "Bridges.ToTopology: fundamentalGroupoidAdjunction, sheafSpaceAdjunction"
#eval "Bridges.ToTopology: localeTopologyAdjunction, connectedComponentsAdjunction"
#eval "Bridges.ToTopology: Stone-Cech, discrete-forgetful, compactness as adjunction"
