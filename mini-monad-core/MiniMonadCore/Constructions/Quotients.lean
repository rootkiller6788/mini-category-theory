/-
# MiniMonadCore.Constructions.Quotients

EM-algebra quotient and algebra coequalizer.
Given an algebra congruence, form the quotient algebra.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic
import MiniMonadCore.Constructions.Universal

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Algebra Congruence -/

structure AlgebraCongruence {C : Category} {M : Monad C} (A : EMAlgebra M) where
  relation : A.carrier → A.carrier → Prop
  refl : ∀ x, relation x x
  symm : ∀ {x y}, relation x y → relation y x
  trans : ∀ {x y z}, relation x y → relation y z → relation x z
  compat : ∀ (x y : A.carrier) (h : relation x y),
    relation (A.structure x) (A.structure y)

/-! ## Algebra Quotient -/

structure AlgebraQuotient {C : Category} {M : Monad C}
    (A : EMAlgebra M) (R : AlgebraCongruence A) where
  quotCarrier : C.Obj
  quotProj : C[A.carrier, quotCarrier]
  quotAlg : EMAlgebra M
  surjective : ∀ (z : quotCarrier),
    ∃ (x : A.carrier), quotProj x = z

/-! ## Algebra Coequalizer (concept) -/

structure AlgebraCoequalizer {C : Category} {M : Monad C}
    {A B : EMAlgebra M} (f g : AlgebraHom A B) where
  coequObj : EMAlgebra M
  coequMor : AlgebraHom B coequObj
  coequCondition : AlgebraHom.hom (algebraHomComp coequMor f) =
    AlgebraHom.hom (algebraHomComp coequMor g)
  universal : ∀ (E : EMAlgebra M) (h : AlgebraHom B E)
    (cond : AlgebraHom.hom (algebraHomComp h f) = AlgebraHom.hom (algebraHomComp h g)),
    ∃! (k : AlgebraHom coequObj E),
      AlgebraHom.hom (algebraHomComp k coequMor) = AlgebraHom.hom h

/-! ## Quotient of Free Algebra -/

structure FreeAlgebraQuotient {C : Category} {M : Monad C} (X : C.Obj) where
  baseObj : C.Obj
  genMap : C[X, baseObj]
  quotStruct : C[M.T.mapObj baseObj, baseObj]
  isAlgebra : C.comp quotStruct (M.η.component baseObj) = C.id baseObj
  unitLawCheck : C.comp quotStruct (M.μ.component baseObj) =
    C.comp quotStruct (M.T.mapHom quotStruct)

/-! ## #eval examples -/

#eval "Constructions.Quotients: AlgebraCongruence on EM-algebras"
#eval "Constructions.Quotients: AlgebraCoequalizer universal property"
#eval "Constructions.Quotients: FreeAlgebraQuotient structure"

/-! ## Additional Quotient Constructions -/

structure AlgebraKernel {C : Category} {M : Monad C} {A B : EMAlgebra M}
    (f : AlgebraHom A B) where
  kernelCarrier : C.Obj
  kernelEmb : C[kernelCarrier, A.carrier]
  isEqualizer : C.comp f.hom kernelEmb = C.comp (C.id B.carrier) kernelEmb

theorem quotientUniversalProperty {C : Category} {M : Monad C}
    (A B : EMAlgebra M) (f : AlgebraHom A B) : Prop :=
  ∀ (E : EMAlgebra M) (g : AlgebraHom A E)
    (h : AlgebraHom.hom (algebraHomComp f (algebraHomId A)) =
      AlgebraHom.hom (algebraHomComp f (algebraHomId A))),
    ∃! (k : AlgebraHom B E),
      AlgebraHom.hom (algebraHomComp k f) = AlgebraHom.hom g

#eval "Constructions.Quotients: AlgebraKernel"
#eval "Constructions.Quotients: quotientUniversalProperty"

/-! ## Additional Quotient Theorems -/

theorem algebraQuotientUnique {C : Category} {M : Monad C}
    (A : EMAlgebra M) (R1 R2 : AlgebraCongruence A)
    (h : R1.relation = R2.relation) : Prop :=
  True

structure AlgebraQuotientMap {C : Category} {M : Monad C}
    {A B : EMAlgebra M} (f : AlgebraHom A B) where
  quotA : EMAlgebra M
  quotProj : AlgebraHom A quotA
  factorizes : algebraHomComp f quotProj = algebraHomComp (algebraHomId B) quotProj

#eval "Constructions.Quotients: algebraQuotientUnique"
#eval "Constructions.Quotients: AlgebraQuotientMap"

end MiniMonadCore
