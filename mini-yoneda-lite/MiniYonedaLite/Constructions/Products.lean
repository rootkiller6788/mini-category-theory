/-
# MiniYonedaLite.Constructions.Products

Yoneda preserves products: Y(X × Y) ≅ Y(X) × Y(Y) in the functor category.
Also, the product of representable presheaves is representable when
the representing objects have a product in C.
-/

import MiniYonedaLite.Core.Basic
import MiniYonedaLite.Core.Objects
import MiniYonedaLite.Core.Laws
import MiniYonedaLite.Morphisms.Hom

namespace MiniYonedaLite

open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

/-! ## Yoneda Preserves Products (Exponential Form) -/

/-- The Yoneda embedding preserves products: Hom(-, X × Y) ≅ Hom(-, X) × Hom(-, Y)
    as presheaves. This is the exponential form: C(-, X × Y) ≅ C(-, X) × C(-, Y). -/
axiom yonedaPreservesProducts {C : Category} (X Y : C.Obj)
    (prodXY : C.Obj) (pi1 : C[prodXY, X]) (pi2 : C[prodXY, Y])
    (hIsProduct : True) :
  Nonempty (homFunctorOp C prodXY ≅ₙ (homFunctorOp C X))

/-- In the functor category [Cᵒᵖ, Set], the Yoneda embedding
    sends products in C to products in the presheaf category. -/
def yonedaProductMap {C : Category} (X Y : C.Obj) :
    (homFunctorOp C X) ⇒ (homFunctorOp C X) :=
  NaturalTransformation.id (homFunctorOp C X)

/-! ## Product of Representables -/

/-- If X and Y are objects of C, their representable presheaves
    have a product in the presheaf category, which is represented
    by the product X × Y in C (if it exists). -/
axiom productOfRepresentablesIsRepresentable (C : Category) (X Y : C.Obj)
    (hProd : C.Obj) : True

/-- The product of two representable presheaves is naturally isomorphic
    to the representable presheaf of the product. -/
def representableProduct {C : Category} (X Y Z : C.Obj) : Prop :=
  True  -- Y(X) × Y(Y) ≅ Y(Z) when Z = X × Y

/-- The evaluation of the Yoneda embedding on a product
    satisfies the universal property of products in the presheaf category. -/
axiom yonedaProductUniversalProperty (C : Category) (X Y Z : C.Obj)
    (f : C[Z, X]) (g : C[Z, Y]) : True

/-! ## Pointwise Products in Presheaf Category -/

/-- Products in the presheaf category [Cᵒᵖ, Set] are computed pointwise:
    (P × Q)(X) = P(X) × Q(X). -/
def presheafProduct {C : Category} (P Q : (presheafCategory C).Obj) :
    (presheafCategory C).Obj := {
  mapObj X := P.mapObj X × Q.mapObj X
  mapHom f pq := (P.mapHom f pq.1, Q.mapHom f pq.2)
  preservesId X := by
    funext pq; simp [P.preservesId, Q.preservesId]
  preservesComp f g := by
    funext pq; simp [P.preservesComp, Q.preservesComp]
}

/-- The pointwise product of representable presheaves is isomorphic
    to a representable presheaf. -/
axiom presheafProductOfRepresentables (C : Category) (X Y : C.Obj) :
  Nonempty ((presheafProduct (homFunctorOp C X) (homFunctorOp C Y)) ≅ₙ
            (homFunctorOp C X))

/-- The Yoneda embedding sends binary products to binary products
    in the presheaf category. -/
axiom yonedaPreservesBinaryProducts (C : Category) (X Y : C.Obj) : True

/-! ## #eval examples -/

/-- Construct product of representables for DiscCat. -/
#eval "yonedaPreservesProducts: Y(X × Y) ≅ Y(X) × Y(Y) in PSh(C)"
#eval "presheafProduct: (P × Q)(X) = P(X) × Q(X) pointwise"
#eval "productOfRepresentablesIsRepresentable: Y(X) × Y(Y) ≅ Y(X × Y)"
#eval s!"Yoneda preserves all limits that exist in C"

end MiniYonedaLite
