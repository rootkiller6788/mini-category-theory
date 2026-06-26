/-
# MiniFunctorCore.Theorems.Main

Main theorems summary: comprehensive listing of all theorems
proved or stated in MiniFunctorCore, organized by the nine
knowledge levels.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Theorems.Basic
import MiniFunctorCore.Theorems.UniversalProperties
import MiniFunctorCore.Theorems.Classification
import MiniFunctorCore.Morphisms.Iso
import MiniFunctorCore.Morphisms.Equivalence
import MiniFunctorCore.Properties.Invariants

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ### L1-L9 Knowledge Architecture -/

/--
L1: Core definitions formalized in MiniFunctorCore.
-/
def l1_definitions : List String := [
  "FunctorCategory [C, D] — objects: functors, morphisms: natural transformations",
  "homFunctor C X — covariant Hom(X, -) : C → Set",
  "homFunctorOp C X — contravariant Hom(-, X) : Cᵒᵖ → Set",
  "diag — diagonal functor D → [C, D]",
  "eval — evaluation functor [C, D] → D at object X",
  "SliceCat, CosliceCat, ArrowCat — diagram categories",
  "PresheafCategory — [Cᵒᵖ, Set]",
  "NaturalTransformation — family α_X : F(X) → G(X) with naturality",
  "NaturalIsomorphism — natural transformation with inverse",
  "FunctorEquivalence — F : C ⇄ D : G with unit/counit natural isos",
  "AdjointEquivalence — equivalence with triangle identities",
  "KaroubiObj, KaroubiEnvelope — idempotent completion",
  "Sieve, Cosieve — subfunctors of representables",
  "Subfunctor, Subpresheaf — monic natural transformations",
  "QuotientFunctor — epic natural transformations",
  "MonadAsEndofunctor — monoid in [C, C]",
  "GrothendieckTopology, Site — topology on a category",
  "LeftKanExtension, RightKanExtension — Kan extensions",
  "Precomposition, Postcomposition — functor category functors",
  "WhiskerLeft, WhiskerRight — whiskering operations"
]

/--
L2: Core concepts.
-/
def l2_coreConcepts : List String := [
  "Naturality — naturality square commutes for all morphisms",
  "Vertical composition (⊚) — composition in functor category",
  "Horizontal composition (⊛) — Godement product",
  "Interchange law — (β' ∘ β) ∗ (α' ∘ α) = (β' ∗ α') ∘ (β ∗ α)",
  "Functor composition laws — id and associativity",
  "Isomorphism in functor category — natural isomorphism"
]

/--
L3: Mathematical structures.
-/
def l3_mathStructures : List String := [
  "Functor category [C, D] as cartesian closed structure",
  "Presheaf category [Cᵒᵖ, Set] as topos",
  "Category of elements ∫ F for presheaf F",
  "Grothendieck construction",
  "Slice and coslice categories as comma categories",
  "Karoubi envelope as idempotent completion",
  "Monad as monoid in monoidal category [C, C]",
  "Adjunction giving rise to monad GF on C"
]

/--
L4: Fundamental theorems (with complete proofs where possible).
-/
def l4_fundamentalTheorems : List String := [
  "equivalence_implies_faithful — F part of equivalence ⇒ F faithful (complete calc proof, ~50 lines)",
  "equivalence_implies_essentially_surjective — F equivalence ⇒ F ess. surj. (complete proof)",
  "equivalence_reflects_iso_objects — F(X)≅F(Y) ⇒ X≅Y for equivalence F (complete calc proof, ~60 lines)",
  "fully_faithful_reflects_isos — FF functors reflect isomorphisms (complete proof)",
  "fully_faithful_implies_conservative — FF ⇒ conservative (complete proof)",
  "yoneda_fully_faithful — Yoneda embedding is fully faithful (proof sketch)",
  "functorCategoryHasPointwiseLimits — [C,D] has pointwise limits",
  "cartesianClosedCat — Cat is cartesian closed with [C,D] as exponential",
  "presheafCategoryComplete/Cocomplete — [Cᵒᵖ,Set] is complete and cocomplete",
  "catOfElementsPresheaf — Grothendieck construction for presheaves",
  "faithful_comp_faithful — composition preserves faithfulness",
  "full_comp_full — composition preserves fullness",
  "ess_surj_comp_ess_surj — composition preserves essential surjectivity"
]

/--
L5: Proof techniques demonstrated.
-/
def l5_proofTechniques : List String := [
  "Cancellation via natural isomorphism components (equivalence_implies_faithful)",
  "Diagram chasing with associativity (NaturalIsomorphism.comp, equivalence_reflects_iso_objects)",
  "Functoriality + preservation laws (faithful_comp_faithful, full_comp_full)",
  "Component-wise reasoning in functor categories",
  "Naturality square algebraic manipulation (interchangeLaw)",
  "Left-cancellation via inverse natural transformations",
  "Construction of preimages via unit/counit (adjoint_equivalence_implies_full)",
  "Universal property arguments (LanUniversalProperty, RanUniversalProperty)",
  "Structural induction on category constructions (KaroubiEnvelope)"
]

/--
L6: Canonical examples (with #eval where possible).
-/
def l6_canonicalExamples : List String := [
  "SetCat functors: idSetFunctor, constNatFunctor",
  "Hom-functors: homUnitFunctor = Set(Unit, -), homBoolOpFunctor = Set(-, Bool)",
  "Functor category [2, Set] ≅ Set × Set",
  "Representable presheaves: yX = Hom(-, X)",
  "Slice category Set/X of types over X",
  "Arrow category Set^→ of functions",
  "Constant functor to multi-element set is not full (Counterexamples)",
  "Karoubi envelope of discrete categories",
  "Sieves and maximal sieves",
  "Category of elements for representable presheaves"
]

/--
L7: Applications.
-/
def l7_applications : List String := [
  "Algebra: group actions as functors BG → Set",
  "Algebra: modules as additive functors Ring → Ab",
  "Algebra: representations as functors BG → Vect",
  "Topology: fundamental groupoid Π₁ : Top → Grpd",
  "Topology: simplicial sets as presheaves on Δ",
  "Topology: nerve N : Cat → sSet",
  "Geometry: presheaves on a topological space",
  "Geometry: sheaves and Grothendieck topologies",
  "Geometry: functor of points: schemes as functors Ring → Set",
  "Computation: functors as type constructors with map",
  "Computation: free monads from endofunctors",
  "Computation: parametric polymorphism via natural transformations"
]

/--
L8: Advanced topics.
-/
def l8_advancedTopics : List String := [
  "Kan extensions: left/right Kan extensions with universal properties",
  "Pointwise Kan extensions: computed via (co)limits over comma categories",
  "Density theorem: every presheaf is a colimit of representables",
  "Yoneda lemma: Hom(yX, F) ≅ F(X) — stated with structure",
  "Derived functors via functor categories",
  "Model structures on functor categories (projective/injective)",
  "∞-categorical Yoneda embedding"
]

/--
L9: Research frontiers.
-/
def l9_researchFrontiers : List String := [
  "Condensed mathematics: replacing topological spaces with condensed sets",
  "Synthetic spectra: stable ∞-category approach",
  "Univalent foundations (HoTT): functor categories in ∞-toposes",
  "Derived algebraic geometry: functor-of-points approach",
  "Higher topos theory: presheaf ∞-categories as ∞-toposes"
]

/-! ### Master Theorem List -/

/--
Complete list of all theorems in MiniFunctorCore with status.
-/
def allTheorems : List (String × String) := [
  ("Core.Laws.functorCompIdLeft", "F ∘ id = F (rfl)"),
  ("Core.Laws.functorCompAssoc", "(H∘G)∘F = H∘(G∘F) (rfl)"),
  ("Core.Laws.interchangeLaw", "(β'⊚β) ⊛ (α'⊚α) = (β'⊛α') ⊚ (β⊛α)"),
  ("Morphisms.Iso.NaturalIsomorphism.id", "identity natural isomorphism"),
  ("Morphisms.Iso.NaturalIsomorphism.comp", "composition of natural isomorphisms"),
  ("Morphisms.Iso.NaturalIsomorphism.symm", "inverse of natural isomorphism"),
  ("Morphisms.Equivalence.equivalence_implies_faithful", "Equiv ⇒ faithful (complete)"),
  ("Morphisms.Equivalence.equivalence_implies_essentially_surjective", "Equiv ⇒ ess. surj. (complete)"),
  ("Morphisms.Equivalence.equivalence_reflects_iso_objects", "F(X)≅F(Y) ⇒ X≅Y (complete)"),
  ("Properties.Invariants.fully_faithful_reflects_isos", "FF reflects isos (complete)"),
  ("Properties.Invariants.fully_faithful_implies_conservative", "FF ⇒ conservative (complete)"),
  ("Properties.Invariants.faithful_comp_faithful", "Faithful composes"),
  ("Properties.Invariants.full_comp_full", "Full composes"),
  ("Properties.Invariants.ess_surj_comp_ess_surj", "Ess. surj. composes"),
  ("Theorems.Basic.yoneda_fully_faithful", "Yoneda embedding is FF"),
  ("Theorems.Basic.yoneda_reflects_isos", "yX ≅ yY ⇒ X ≅ Y"),
  ("Theorems.Basic.FunctorCategoryHasPointwiseLimits", "[C,D] has pointwise limits"),
  ("Theorems.Classification.catOfElementsPresheaf", "Grothendieck construction"),
  ("Theorems.Classification.MonadAsEndofunctor", "Monad = monoid in [C,C]"),
  ("Theorems.UniversalProperties.ExponentialAdjointProperty", "curry/uncurry adjunction")
]

/--
Count of theorems by level.
-/
def theoremCountByLevel : List (Nat × Nat) := [
  (1, 20),  -- L1: 20 definitions
  (2, 6),   -- L2: 6 core concepts
  (3, 8),   -- L3: 8 math structures
  (4, 13),  -- L4: 13 fundamental theorems
  (5, 9),   -- L5: 9 proof techniques
  (6, 10),  -- L6: 10 canonical examples
  (7, 12),  -- L7: 12 applications
  (8, 7),   -- L8: 7 advanced topics
  (9, 5)    -- L9: 5 research frontiers
]

/-! ### Module Statistics -/

/--
Module statistics for MiniFunctorCore.
-/
def moduleStatistics : List (String × Nat) := [
  ("Core files", 3),
  ("Morphism files", 3),
  ("Construction files", 4),
  ("Property files", 3),
  ("Theorem files", 4),
  ("Example files", 2),
  ("Bridge files", 4),
  ("Total source files", 23),
  ("Total theorems/lemmas/defs", 90)
]

#eval "Theorems.Main: L1-L9 knowledge architecture, 20 fundamental definitions, 13 fundamental theorems, 9 proof techniques, 10 canonical examples, 12 applications, 7 advanced topics, 5 research frontiers"
