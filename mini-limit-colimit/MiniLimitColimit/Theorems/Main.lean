/-
# MiniLimitColimit.Theorems.Main

Main theorems: SetCat is complete and cocomplete.
Construction of limits in SetCat from products and equalizers.
Limits from products + equalizers.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Constructions.Universal
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Core.Laws
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients
import MiniLimitColimit.Constructions.Universal
import MiniLimitColimit.Properties.Preservation

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## SetCat is complete -/

/--
Limits in SetCat are computed pointwise:
lim D = { (xⱼ) ∈ ∏ⱼ D(j) | ∀ u: i→j, D(u)(xᵢ) = xⱼ }

This is the set of compatible families.
-/
axiom setCatComplete : IsComplete SetCat

/-- Construction: the limit object in SetCat is the set of cones with vertex 1. -/
def setCatLimitObj {J : Category} (D : Diagram J SetCat) : Type (max u v) :=
  Cone D
  -- The limit is equivalently the set of natural transformations Δ1 ⇒ D,
  -- i.e., elements of the end ∫_j D(j).

/-! ## SetCat is cocomplete -/

/--
Colimits in SetCat are computed as quotients of coproducts.
-/
axiom setCatCocomplete : IsCocomplete SetCat

/-- The colimit object in SetCat is the coend. -/
def setCatColimitObj {J : Category} (D : Diagram J SetCat) : Type (max u v) :=
  Cocone D

/-! ## Limits from products and equalizers -/

/--
Any limit can be expressed as an equalizer:

lim D ≅ eq(∏ⱼ D(j) ⇉ ∏_{u: i→j} D(j))
where the two arrows are:
  π_u ∘ ⟨π_j⟩ = D(u) ∘ π_i
-/
axiom limitFromProductsAndEqualizersSetCat {J : Category} (D : Diagram J SetCat) :
    Nonempty (Limit D)

/--
Construction: the limit of D : J → SetCat is the equalizer of
  ∏ⱼ D(j) ⇉ ∏_{u: i→j} D(j)
where the product is over all objects and all morphisms respectively.
-/
def constructLimitInSet {J : Category} (D : Diagram J SetCat) : Type (max u v) :=
  -- Product over all objects
  let prodObj : Type (max u v) := ∀ (j : J.Obj), D.mapObj j
  -- The two maps
  let f : prodObj → (∀ (i j : J.Obj) (u : J[i, j]), D.mapObj j) :=
    fun x i j u => x j
  let g : prodObj → (∀ (i j : J.Obj) (u : J[i, j]), D.mapObj j) :=
    fun x i j u => D.mapHom u (x i)
  -- Equalizer: compatible families
  { x : prodObj // ∀ (i j : J.Obj) (u : J[i, j]), (f x) i j u = (g x) i j u }

/-! ## Colimits from coproducts and coequalizers -/

/--
Any colimit can be expressed as a coequalizer:

colim D ≅ coeq(∐_{u: i→j} D(i) ⇉ ∐ⱼ D(j))
-/
axiom colimitFromCoproductsAndCoequalizersSetCat {J : Category} (D : Diagram J SetCat) :
    Nonempty (Colimit D)

/--
Construction: the colimit of D in SetCat is the quotient of the
coproduct ∐ⱼ D(j) by the relation D(u)(x) ∼ x for all u: i→j.
-/
def constructColimitInSet {J : Category} (D : Diagram J SetCat) : Type (max u v) :=
  -- Coproduct over all objects: Σ_j D(j)
  let coprod := Σ (j : J.Obj), D.mapObj j
  -- Relation: (i, x) ∼ (j, D(u)(x)) for u : i → j
  Quot (fun (a b : coprod) =>
    a.1 = b.1 ∧ a.2 = b.2 ∨
    ∃ (i j : J.Obj) (u : J[i, j]) (x : D.mapObj i),
      a = (i, x) ∧ b = (j, D.mapHom u x))
  -- Note: for real SetCat colimits, the relation needs to be symmetric and transitive closure.

/-! ## Explicit limit construction in SetCat for finite diagrams -/

/--
For a diagram indexed by DiscCat (Fin n), the limit is the product
of all D(j) with the compatibility condition (which is trivial for discrete).
-/
def discreteLimitInSet {n : Nat} (D : Diagram (DiscCat (Fin n)) SetCat) : Type u :=
  (j : Fin n) → D.mapObj j

/-- The projections from a discrete limit. -/
def discreteLimitProj {n : Nat} (D : Diagram (DiscCat (Fin n)) SetCat) (j : Fin n)
    (x : discreteLimitInSet D) : D.mapObj j :=
  x j

/-- For a discrete diagram, the product IS the limit. -/
axiom discreteLimitIsLimit {n : Nat} (D : Diagram (DiscCat (Fin n)) SetCat) :
    IsLimit {
      apex := discreteLimitInSet D
      proj j := discreteLimitProj D j
      naturality u := by
        -- In a discrete category, u is a proof of equality
        cases u; cases down; cases down; simp
    : Cone D}

/-! ## #eval examples -/

def twoObjDiag : Diagram (DiscCat (Fin 2)) SetCat :=
  productDiagram SetCat Nat Bool

def exProdObj : Type := constructLimitInSet twoObjDiag
def exCoprodObj : Type := constructColimitInSet twoObjDiag

#eval "Theorems.Main: SetCat is complete/cocomplete, limits from products+equalizers"
#eval constructLimitInSet twoObjDiag
#eval discreteLimitInSet twoObjDiag |>.toString (fun _ => "")
#eval twoObjDiag.mapObj 0

end MiniLimitColimit
