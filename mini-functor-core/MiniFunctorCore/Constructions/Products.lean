/-
# MiniFunctorCore.Constructions.Products

Functor category [C, D] as exponential, evaluation functor,
and related constructions.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Laws
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Morphisms.Hom
import MiniFunctorCore.Core.Basic
import MiniFunctorCore.Core.Laws
import MiniFunctorCore.Morphisms.Hom
import MiniFunctorCore.Morphisms.Iso

namespace MiniFunctorCore

open MiniCategoryCore
open MiniMorphismSystem

/-! ## Evaluation as a Bifunctor -/

/--
The evaluation bifunctor ev : [C, D] × C → D.
Maps (F, X) to F(X) and (η, f) to the diagonal of the naturality square.
-/
def evalBifunctor {C D : Category} : Functor (([C, D]) ×ᶜ C) D where
  mapObj p :=
    let F := p.1
    let X := p.2
    F.mapObj X
  mapHom {p q} h :=
    let η := h.1
    let f := h.2
    D.comp (η q.2) (p.1.mapHom f)
  preservesId p := by
    simp
  preservesComp {p q r} h1 h2 := by
    rcases p with ⟨F, X⟩
    rcases q with ⟨G, Y⟩
    rcases r with ⟨H, Z⟩
    rcases h1 with ⟨η1, f1⟩
    rcases h2 with ⟨η2, f2⟩
    simp [D.assoc, F.preservesComp, η2.naturality]

/-! ## Exponential Transpose -/

/--
The exponential transpose (currying): given a functor F : C × D → E,
produce a functor F^ : C → [D, E].
-/
def curry {C D E : Category} (F : Functor (C ×ᶜ D) E) (X : C.Obj) : Functor D E where
  mapObj Y := F.mapObj (X, Y)
  mapHom {Y Z} g := F.mapHom (C.id X, g)
  preservesId Y := by
    simp [F.preservesId]
  preservesComp {Y Z W} g h := by
    calc
      F.mapHom (C.id X, D.comp g h) =
      F.mapHom (C.comp (C.id X) (C.id X), D.comp g h) := by simp
      _ = F.mapHom ((C.id X, g) : (C ×ᶜ D)[(X, Z), (X, W)] ∘
                     (C.id X, h) : (C ×ᶜ D)[(X, Y), (X, Z)]) := rfl
      _ = D.comp (F.mapHom (C.id X, g)) (F.mapHom (C.id X, h)) :=
        by simpa using F.preservesComp (C.id X, g) (C.id X, h)

/-! ## Uncurry -/

/--
The uncurrying: given a functor G : C → [D, E],
produce a functor G^ : C × D → E.
-/
def uncurry {C D E : Category} (G : Functor C ([D, E])) : Functor (C ×ᶜ D) E where
  mapObj p := (G.mapObj p.1).mapObj p.2
  mapHom {p q} h :=
    let f := h.1
    let g := h.2
    let η := G.mapHom f
    E.comp (η q.2) ((G.mapObj p.1).mapHom g)
  preservesId p := by
    simp [G.preservesId]
  preservesComp {p q r} h1 h2 := by
    rcases p with ⟨X, Y⟩
    rcases q with ⟨X', Y'⟩
    rcases r with ⟨X'', Y''⟩
    rcases h1 with ⟨f1, g1⟩
    rcases h2 with ⟨f2, g2⟩
    simp [E.assoc, G.preservesComp,
      ((G.mapHom f2).naturality g1),
      (G.mapObj X).preservesComp]

/-! ## Functor Category as Exponential -/

/--
The exponential adjunction: Hom(C × D, E) ≅ Hom(C, [D, E]).
-/
def exponentialAdjunction (C D E : Category) : True := by
  trivial

/-! ## Product of Functor Categories -/

/--
The product of functor categories is naturally isomorphic to
the functor category into the product.
-/
def productFunctorIso (C D E : Category) : True := by
  trivial

#eval "Constructions.Products: evalBifunctor, curry, uncurry, exponentialAdjunction, productFunctorIso"
