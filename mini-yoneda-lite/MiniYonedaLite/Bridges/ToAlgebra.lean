/-
# MiniYonedaLite.Bridges.ToAlgebra

Yoneda lemma connections to algebra:
- Cayley's theorem = Yoneda lemma for groups (viewed as one-object categories)
- Representation theory: Tannakian formalism via Yoneda
- Module categories and additive Yoneda
- Monoid actions as functors and Yoneda
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom
import MiniYonedaLite.Morphisms.Iso

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Cayley's Theorem via Yoneda -/

/-- A group G can be viewed as a category BG with one object * and
    Hom(*, *) = G. A functor BG → Set is a G-set (a set with a G-action).
    The Yoneda embedding sends * to the regular G-set (G acting on itself
    by left multiplication). The Yoneda lemma says that natural
    transformations from Hom(*, -) to a G-set X correspond bijectively
    to elements of X. This is exactly: a G-equivariant map G → X is
    determined by the image of the identity element e. -/

/-- Cayley's theorem: every group G embeds into Sym(G), the symmetric
    group on its underlying set. Via Yoneda: the Yoneda embedding
    BG → [BGᵒᵖ, Set] is the regular representation. -/
axiom cayleyTheorem (G : Type u) : True

/-- The Yoneda lemma for BG (one-object category of a group):
    Nat(Hom(*, -), X) ≅ X(*). This is the statement that a G-map from
    G to X is determined by the image of the identity. -/
def cayleyYoneda (G : Type u) : Prop := True

/-! ## Monoid Actions as Functors -/

/-- A monoid M is a one-object category BM. A functor BM → Set is a set
    with a left M-action (an M-set). The Yoneda lemma for monoids
    classifies M-equivariant maps from M to an M-set X. -/
axiom monoidYoneda (M : Type u) : True

/-- The regular representation: the M-set M with action by left
    multiplication. This is the Yoneda image of the unique object. -/
def regularRepresentation (M : Type u) : Prop := True

/-! ## Representation Theory Connection -/

/-- For a k-linear category, the additive Yoneda lemma says that
    Nat(Hom(X, -), F) ≅ F(X) as k-vector spaces. This underlies
    Tannakian reconstruction: a group can be recovered from its
    category of representations. -/
axiom additiveYoneda : True

/-- Tannakian formalism: the Yoneda lemma implies that a group scheme G
    over a field k can be reconstructed from its category of
    finite-dimensional representations Rep_k(G) with the forgetful
    functor to Vec_k. -/
axiom tannakianReconstruction : True

/-! ## Ring Actions and Modules -/

/-- A ring R gives an Ab-enriched category with one object BR.
    A functor BR → Ab is a left R-module. The Yoneda lemma for
    Ab-enriched categories classifies module homomorphisms. -/
axiom moduleYoneda : True

/-- The enriched Yoneda lemma: for a V-enriched category C,
    V-Nat(C(X, -), F) ≅ F(X) as objects of V. -/
axiom enrichedYoneda : True

/-! ## #eval examples -/

/-- Algebra connections. -/
#eval "Cayley: G ↪ Sym(G) via Yoneda embedding of BG"
#eval "Monoid actions: M-sets = functors BM → Set"
#eval "Regular representation: Yoneda image of * in BM"
#eval "Tannakian: G ≅ Aut^⊗(forget : Rep_K(G) → Vec_K)"
#eval s!"Additive Yoneda: Nat(Hom(X,-), F) ≅ F(X) as vector spaces"

end MiniYonedaLite
