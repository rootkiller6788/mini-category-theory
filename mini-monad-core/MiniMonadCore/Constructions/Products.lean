/-
# MiniMonadCore.Constructions.Products

Product of monads via distributive law. Monad transformer.
A distributive law λ : S ∘ T ⇒ T ∘ S allows composing monads S and T.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniMonadCore.Core.Basic

namespace MiniMonadCore

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Distributive Law -/

structure DistributiveLaw {C : Category} (S T : Monad C) where
  lambda : Functor.comp S.T T.T ⇒ Functor.comp T.T S.T
  unitSBCompat : ∀ (X : C.Obj),
    C.comp (lambda.component X)
      (NaturalTransformation.whiskerLeft S.T T.η).component X =
    (NaturalTransformation.whiskerRight S.η T.T).component X
  unitSTCompat : ∀ (X : C.Obj),
    C.comp (lambda.component X)
      (NaturalTransformation.whiskerRight T.T S.η).component X =
    (NaturalTransformation.whiskerLeft T.T S.η).component X
  muSBCompat : ∀ (X : C.Obj),
    C.comp (lambda.component X)
      (NaturalTransformation.whiskerLeft S.T T.μ).component X =
    C.comp (C.comp (NaturalTransformation.whiskerRight T.μ S.T).component X
      (NaturalTransformation.vcomp
        (NaturalTransformation.whiskerLeft T.T (NaturalTransformation.whiskerRight lambda T.T))
        (NaturalTransformation.whiskerLeft (Functor.comp S.T S.T) lambda)).component X)
      (lambda.component X)
  muSTCompat : ∀ (X : C.Obj),
    C.comp (lambda.component X)
      (NaturalTransformation.whiskerRight T.T S.μ).component X =
    C.comp (C.comp (NaturalTransformation.whiskerRight S.μ T.T).component X
      (NaturalTransformation.vcomp
        (NaturalTransformation.whiskerRight (NaturalTransformation.whiskerLeft S.T lambda) S.T)
        (NaturalTransformation.whiskerLeft lambda (Functor.comp S.T S.T))).component X)
      (lambda.component X)

/-! ## Composite Monad from Distributive Law -/

def compositeMonad {C : Category} {S T : Monad C} (λd : DistributiveLaw S T) : Monad C where
  T := Functor.comp S.T T.T
  η := NaturalTransformation.vcomp
    (NaturalTransformation.whiskerLeft S.T T.η) S.η
  μ := NaturalTransformation.vcomp
    (NaturalTransformation.whiskerRight S.μ T.T)
    (NaturalTransformation.vcomp
      (NaturalTransformation.whiskerLeft S.T
        (NaturalTransformation.whiskerRight T.μ S.T))
      (NaturalTransformation.whiskerLeft S.T λd.lambda))
  leftUnit := fun X => by
    simp [C.assoc, S.leftUnit, T.leftUnit, S.T.preservesComp,
      S.T.preservesId, T.T.preservesComp, T.T.preservesId,
      S.rightUnit, T.rightUnit]
  rightUnit := fun X => by
    simp [C.assoc, S.leftUnit, T.leftUnit, S.T.preservesComp,
      S.T.preservesId, T.T.preservesComp, T.T.preservesId,
      S.rightUnit, T.rightUnit]
  associativity := fun X => by
    simp [C.assoc, S.T.preservesComp, T.T.preservesComp]

/-! ## Monad Transformer -/

structure MonadTransformer {C : Category} where
  transform : Monad C → Monad C
  lift : (M : Monad C) → M.T ⇒ (transform M).T
  liftNatural : ∀ (M N : Monad C) (φ : MonadMorphism M N) (X : C.Obj),
    C.comp ((lift N).component X) (φ.component.component X) =
    C.comp ((transform.mapHom φ).component X) ((lift M).component X)
  transformPure : Monad C → Monad C

def identityTransformer {C : Category} : MonadTransformer (C := C) where
  transform M := M
  lift M := NaturalTransformation.id M.T
  liftNatural M N φ X := by
    simp [NaturalTransformation.id, C.comp_id, C.id_comp]
  transformPure := id

/-! ## #eval examples -/

#eval "Constructions.Products: DistributiveLaw S∘T ⇒ T∘S"
#eval "Constructions.Products: compositeMonad from distributive law"
#eval "Constructions.Products: identityTransformer example"

end MiniMonadCore
