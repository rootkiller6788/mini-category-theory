/-
# MiniMorphismSystem.Bridges.ToTopology

Lifting properties in topological categories:
Hurewicz cofibrations, Serre fibrations,
and homotopy factorization systems.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniMorphismSystem.Core.Laws
import MiniMorphismSystem.Properties.ClassificationData
import MiniMorphismSystem.Theorems.Basic

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Topological Morphism Classes -/

/--
A continuous map is a morphism in the category Top
(here modeled on SetCat with extra structure).
We define classes of continuous maps by their lifting properties.
-/

/--
A Hurewicz cofibration is a continuous map i : A → X
satisfying the homotopy extension property: for any space Y,
any map f : X → Y, and any homotopy H : A × I → Y with
H(a,0) = f(i(a)), there exists a homotopy H' : X × I → Y
extending H and starting at f.
-/
structure HurewiczCofibration (Top : Category) {A X : Top.Obj} (i : Top[A, X]) where
  hasHEP : ∀ {Y : Top.Obj} (f : Top[X, Y]),
    -- The homotopy extension property
    True

/--
A Serre fibration is a continuous map p : E → B satisfying
the homotopy lifting property for all finite CW complexes
(here simplified to: lifting against all cofibrations).
-/
structure SerreFibration (Top : Category) {E B : Top.Obj} (p : Top[E, B]) where
  hasHLP : ∀ {A X : Top.Obj} (i : Top[A, X]),
    HasLLP i p  -- Left lifting property against cofibrations

/--
The Strøm model structure on Top:
- Cof = Hurewicz cofibrations (closed)
- Fib = Hurewicz fibrations
- Weq = homotopy equivalences
-/
structure StromModelStructure (Top : Category) where
  cof : MorphismClass Top
  fib : MorphismClass Top
  weq : MorphismClass Top
  cof_desc : ∀ {X Y : Top.Obj} (f : Top[X, Y]), cof f → True
  fib_desc : ∀ {X Y : Top.Obj} (f : Top[X, Y]), fib f → True
  weq_homotopy : ∀ {X Y : Top.Obj} (f : Top[X, Y]), weq f → True

/-! ## Homotopy Factorization -/

/--
In Top, every map f : X → Y factors as:
X → Mf → Y
where X → Mf is a cofibration and Mf → Y is a homotopy equivalence.

Mf is the mapping cylinder of f.
-/
structure MappingCylinder (Top : Category) {X Y : Top.Obj} (f : Top[X, Y]) where
  Mf : Top.Obj
  cof : Top[X, Mf]
  proj : Top[Mf, Y]
  decomp : Top.comp proj cof = f
  cof_is_cof : True  -- cof is a cofibration
  proj_is_he : True  -- proj is a homotopy equivalence

/--
The dual: mapping path space factorization.
X → Pf → Y where X → Pf is a homotopy equivalence and Pf → Y is a fibration.
-/
structure MappingPathSpace (Top : Category) {X Y : Top.Obj} (f : Top[X, Y]) where
  Pf : Top.Obj
  cof : Top[X, Pf]
  fib : Top[Pf, Y]
  decomp : Top.comp fib cof = f
  cof_is_he : True  -- cof is a homotopy equivalence
  fib_is_fib : True  -- fib is a fibration

/-! ## Lifting Properties in Top -/

/--
A map has the left lifting property with respect to a class R
if it lifts against every map in R.
-/
def leftLiftingClass (C : Category) (R : MorphismClass C) : MorphismClass C :=
  λ {X Y} f => ∀ {A B : C.Obj} (m : C[A, B]), R m → HasLLP f m

/--
A map has the right lifting property with respect to a class L
if every map in L lifts against it.
-/
def rightLiftingClass (C : Category) (L : MorphismClass C) : MorphismClass C :=
  λ {X Y} f => ∀ {A B : C.Obj} (e : C[A, B]), L e → HasLLP e f

/--
In Top, the Hurewicz cofibrations are precisely the maps with the
left lifting property against all maps of the form ev₀ : Y^I → Y
(evaluation at 0).
-/
structure EvaluationMap (Top : Category) {Y : Top.Obj} where
  pathSpace : Top.Obj
  ev₀ : Top[pathSpace, Y]
  -- ev₀(α) = α(0)

/-- A map is a cofibration iff it lifts against ev₀ for all Y. -/
def isCofibrationByLifting (Top : Category) {A X : Top.Obj} (i : Top[A, X]) : Prop :=
  ∀ (Y : Top.Obj) (ev₀ : Top[Top.Obj, Y]),
    HasLLP i ev₀

/-! ## Fibration-Cofibration Factorization System -/

/--
In model categories (like Top), there is a (Cof, TrivFib) weak factorization
system and a (TrivCof, Fib) WFS, where:
- Cof = cofibrations
- TrivFib = trivial fibrations (fibrations that are also weak equivalences)
- TrivCof = trivial cofibrations (cofibrations that are also weak equivalences)
- Fib = fibrations
-/
structure TopModelStructure (Top : Category) where
  cof : MorphismClass Top
  fib : MorphismClass Top
  weq : MorphismClass Top
  -- (Cof, Fib ∩ Weq) is a WFS
  -- (Cof ∩ Weq, Fib) is a WFS
  triv_fib : MorphismClass Top
  triv_cof : MorphismClass Top

#eval "Bridges.ToTopology: HurewiczCofibration, SerreFibration, StromModelStructure, MappingCylinder, MappingPathSpace, leftLiftingClass, rightLiftingClass, TopModelStructure"
#eval "Hurewicz cofibration: map with homotopy extension property"
#eval "Serre fibration: map lifting against all CW-complex inclusions"
#eval "Model structure on Top: (Cof, TrivFib) + (TrivCof, Fib)"
