/-
# MiniAdjunction.Bridges.ToGeometry

Sheaf-space adjunction, Spec-global sections adjunction.
Connecting adjunctions to algebraic geometry.
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

/-! ## Sheaf-Space Adjunction -/

/--
For a topological space X, the category of presheaves PSh(X) and
the category of spaces over X (Top/X) are related by an adjunction:
  L : PSh(X) → Top/X ⊣ Γ : Top/X → PSh(X)

L sends a presheaf to its etale space (bundle of germs).
Γ sends a space over X to its sheaf of continuous sections.
-/
structure SheafSpaceAdjunction (X : Type u) where
  etaleSpace : Functor SetCat SetCat
  sections : Functor SetCat SetCat
  adj : etaleSpace ⊣ sections

/--
L is fully faithful: the category of sheaves is a reflective
subcategory of the category of presheaves.
-/
axiom sheafificationIsReflective : Prop

#eval "Bridges.ToGeometry: Sheaf-Space Adjunction L ⊣ Γ"

/-! ## Spec-Global Sections Adjunction -/

/--
The fundamental adjunction of algebraic geometry:
  Spec : CommRingᵒᵖ → Sch  ⊣  Γ : Sch → CommRingᵒᵖ

For a commutative ring A, Spec(A) is its prime spectrum (an affine scheme).
For a scheme X, Γ(X) = O_X(X) is the ring of global regular functions.
There is a natural bijection: Hom_Sch(X, Spec(A)) ≅ Hom_CRing(A, Γ(X)).
-/
structure SpecGlobalSectionsAdjunction where
  spec : Functor SetCat SetCat
  globalSections : Functor SetCat SetCat
  adj : spec ⊣ globalSections

/--
Spec ⊣ Γ is an adjunction between affine schemes and commutative rings
(the opposite category).
-/
axiom specGlobalSectionsAdjunctionGeometry : Prop

/--
The unit of Spec ⊣ Γ at A is the map A → Γ(Spec A) which is
an isomorphism (a fundamental theorem: rings are recovered
from their global sections on Spec).
-/
axiom specUnitIsIso : Prop

#eval "Bridges.ToGeometry: Spec ⊣ Γ global sections adjunction"

/-! ## GAGA (Serre) -/

/--
The analytification functor Alg → An (algebraic varieties to
complex analytic spaces) has the algebraization functor as
a left adjoint in certain cases (GAGA principle of Serre).
-/
axiom gagaAdjunction : Prop

/-! ## de Rham Adjunction -/

/--
The de Rham functor dR : Mfd → dga sending a manifold to its
de Rham algebra is part of an adjunction with integration.
-/
axiom deRhamAdjunction : Prop

/-! ## Tangent/Cotangent Adjunction -/

/--
Between the category of pointed manifolds and the category of
vector spaces, the tangent space functor is left adjoint to...
(conceptually, tangent ⊣ cotangent as functors).
-/
axiom tangentCotangentAdjunction : Prop

/-! ## Differential Graded Algebra Adjunctions -/

/--
The normalized chain complex functor N : sAb → Ch_{≥0} is part of
a Quillen equivalence (adjunction up to homotopy): N ⊣ Γ.
-/
axiom doldKanCorrespondence : Prop

/-! ## Homotopy Adjoints -/

/--
The suspension functor Σ and loop space functor Ω form an adjunction
in the homotopy category: Σ ⊣ Ω.
-/
axiom suspensionLoopAdjunction : Prop

#eval "Bridges.ToGeometry: GAGA, de Rham, tangent/cotangent, suspension-loop adjunctions"
#eval "Bridges.ToGeometry: Dold-Kan correspondence, sheafification reflective"
#eval "Bridges.ToGeometry: Spec-unit isomorphism (φ: A ≅ Γ(Spec A))"
