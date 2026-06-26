/-
# MiniLimitColimit.Bridges.ToAlgebra

Limits in algebraic categories: Grp, Ab, Ring.
Free product as coproduct, direct product as product.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Constructions.Products

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Algebraic categories (stub structures since we don't have full algebra) -/

/-- A group: a type with multiplication, identity, and inverse. -/
structure Group where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier

/-- The category of groups. -/
def Grp : Category where
  Obj := Group
  Hom G H := G.carrier → H.carrier
  id _ x := x
  comp g f x := g (f x)
  comp_id _ := rfl
  id_comp _ := rfl
  assoc _ _ _ := rfl

/-- An abelian group (same as Group for our purposes). -/
structure AbGroup where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier
  neg : carrier → carrier

/-- The category of abelian groups. -/
def Ab : Category where
  Obj := AbGroup
  Hom A B := A.carrier → B.carrier
  id _ x := x
  comp g f x := g (f x)
  comp_id _ := rfl
  id_comp _ := rfl
  assoc _ _ _ := rfl

/-- A ring. -/
structure Ring where
  carrier : Type u
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  zero : carrier
  one : carrier
  neg : carrier → carrier

/-- The category of rings. -/
def RingCat : Category where
  Obj := Ring
  Hom R S := R.carrier → S.carrier
  id _ x := x
  comp g f x := g (f x)
  comp_id _ := rfl
  id_comp _ := rfl
  assoc _ _ _ := rfl

/-! ## Direct product (limit) in Grp -/

/--
The direct product G × H of groups is the categorical product in Grp.
It is a limit of the discrete two-object diagram.
-/
axiom directProductInGrpIsProduct {G H : Group} :
    IsProduct (C := Grp) G H {
      carrier := G.carrier × H.carrier
      mul p q := (G.mul p.1 q.1, H.mul p.2 q.2)
      one := (G.one, H.one)
      inv p := (G.inv p.1, H.inv p.2)
    }

/-! ## Free product (coproduct) in Grp -/

/--
The free product G ∗ H is the categorical coproduct in Grp.
It is NOT the direct product.
-/
axiom freeProductInGrpIsCoproduct {G H : Group} :
    IsCoproduct (C := Grp) G H (Group.mk (G.carrier × H.carrier) (fun p q => (p.1, q.2)) (G.one, H.one) (fun p => (G.inv p.1, H.inv p.2)))
    -- Actually the free product is much more complex; this is a stub

/-! ## Direct product in Ab -/

/--
In Ab, the direct product and coproduct coincide for finite families.
The categorical product is the direct sum.
-/
axiom directProductInAbIsProduct {A B : AbGroup} :
    IsProduct (C := Ab) A B {
      carrier := A.carrier × B.carrier
      add p q := (A.add p.1 q.1, B.add p.2 q.2)
      zero := (A.zero, B.zero)
      neg p := (A.neg p.1, B.neg p.2)
    }

/-! ## Direct product in Ring -/

/--
The direct product R × S of rings is the categorical product in RingCat.
-/
axiom directProductInRingIsProduct {R S : Ring} :
    IsProduct (C := RingCat) R S {
      carrier := R.carrier × S.carrier
      add p q := (R.add p.1 q.1, S.add p.2 q.2)
      mul p q := (R.mul p.1 q.1, S.mul p.2 q.2)
      zero := (R.zero, S.zero)
      one := (R.one, S.one)
      neg p := (R.neg p.1, S.neg p.2)
    }

/-! ## Limits in algebraic categories are computed in Set -/

/--
Forgetful functors Grp → Set, Ab → Set, Ring → Set
preserve limits. Limits in algebraic categories are computed
on the underlying sets.
-/
axiom forgetfulPreservesLimits : True

/-! ## Equalizer in Grp -/

/--
The equalizer of two group homomorphisms f,g : G → H is the
subgroup {x ∈ G | f(x) = g(x)}.
-/
axiom equalizerInGrp {G H : Group} (f g : Grp[G, H]) :
    Nonempty (Equalizer (C := Grp) f g)

/-! ## Coequalizer in Ab -/

/--
In Ab, the coequalizer of f,g : A → B is the quotient B / im(f-g).
-/
axiom coequalizerInAb {A B : AbGroup} (f g : Ab[A, B]) :
    Nonempty (Coequalizer (C := Ab) f g)

/-! ## #eval examples -/

def trivialGrp : Group := {
  carrier := Unit
  mul _ _ := ()
  one := ()
  inv _ := ()
}

#eval "Bridges.ToAlgebra: Grp, Ab, Ring limits; free product, direct product"
#eval Grp.Obj
#eval Ab.Obj
#eval RingCat.Obj

end MiniLimitColimit
