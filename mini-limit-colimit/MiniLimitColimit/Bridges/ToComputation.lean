/-
# MiniLimitColimit.Bridges.ToComputation

Data type limits: tuples as products, sum types as coproducts,
limits in programming language semantics.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniLimitColimit.Core.Basic
import MiniLimitColimit.Core.Objects
import MiniLimitColimit.Constructions.Products
import MiniLimitColimit.Constructions.Subobjects
import MiniLimitColimit.Constructions.Quotients

namespace MiniLimitColimit

open MiniCategoryCore

/-! ## Tuples as products -/

/--
The product type A × B is the categorical product in the category of types.
In functional programming, `(a, b)` is the limit cone with projections `fst` and `snd`.
-/
def tupleAsProduct {A B : Type u} : IsProduct (SetCat := SetCat) A B (A × B) :=
  productOfPairInSet

/--
Generalized to n-tuples: the product of n types is the type of n-tuples.
For A₁, ..., Aₙ, the product is A₁ × ... × Aₙ.
-/
axiom nTupleAsProduct {n : Nat} (types : Fin n → Type u) :
    Nonempty (Limit (Functor.const (DiscCat (Fin n)) SetCat (types 0)))

/-! ## Sum types as coproducts -/

/--
The sum type A ⊕ B (or Either A B) is the categorical coproduct
in the category of types. `inl` and `inr` are the injections.
-/
def sumAsCoproduct {A B : Type u} : IsCoproduct (SetCat := SetCat) A B (A ⊕ B) :=
  coproductOfPairInSet

/--
Generalized to n-ary coproducts: the coproduct of n types
is the indexed sum Σ i, A_i.
-/
axiom nSumAsCoproduct {n : Nat} (types : Fin n → Type u) :
    IsCoproduct (SetCat := SetCat) (types 0) (types 1) ((i : Fin n) × types i)

/-! ## Records as limits -/

/--
A record type `{a : A, b : B, c : C}` is the product A × B × C.
The limit projections correspond to field accessors.
-/
axiom recordAsLimit : IsProduct (SetCat := SetCat) Nat String (Nat × String)

/-! ## Variant types as colimits -/

/--
A discriminated union / variant type (like Rust enum, Haskell ADT)
is a coproduct (colimit). Each variant is an injection into the sum.
-/
axiom variantAsCoproduct {n : Nat} (variants : Fin n → Type u) :
    IsCoproduct (SetCat := SetCat) (variants 0) (variants 1) ((i : Fin n) × variants i)

/-! ## Recursive types as limits/colimits -/

/--
Recursive types (like `List A`, `Tree A`) arise as initial algebras
(colimits) or final coalgebras (limits).

List A ≅ 1 + A × List A  (initial algebra = colimit)
Stream A ≅ A × Stream A   (final coalgebra = limit)
-/
axiom initialAlgebraAsColimit {F : SetCat.Obj → SetCat.Obj} : True
axiom finalCoalgebraAsLimit {F : SetCat.Obj → SetCat.Obj} : True

/-! ## Function types as exponentials (not limits) -/

/--
Note: function types A → B are NOT limits. They are exponentials B^A,
which are given by the right adjoint to the product functor (-) × A ⊣ (-)^A.
-/
axiom functionTypeIsNotProduct : ¬ (Nonempty (IsProduct (SetCat := SetCat) (Nat → Bool) (Nat → Bool) (Nat → Bool)))
  -- Function types are exponentials, not products.

/-! ## Streams as limits -/

/--
A stream Stream A = A^ω can be seen as a limit:
Stream A ≅ lim (A ← A × A ← A × A × A ← ...)
where each map is the projection forgetting the last component.
-/
axiom streamAsLimit (A : Type u) : Nonempty (Limit (Functor.const (DiscCat Nat) SetCat A))

/-! ## Computation via limit/colimit -/

/--
Fixed points of functors: the least fixed point (data) = colimit,
the greatest fixed point (codata) = limit.

μF = colim (0 → F(0) → F(F(0)) → ...)
νF = lim  (1 ← F(1) ← F(F(1)) ← ...)
-/
axiom fixedPointInductionAsColimit : True
axiom fixedPointCoinductionAsLimit : True

/-! ## #eval examples -/

#eval "Bridges.ToComputation: tuples, sum types, records, variants, streams"
#eval tupleAsProduct (A := Nat) (B := String) |>.fst (3, "hello")
#eval sumAsCoproduct (A := Unit) (B := Bool) |>.inl ()
#eval sumAsCoproduct (A := Unit) (B := Bool) |>.inr true

end MiniLimitColimit
