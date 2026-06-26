/-
# MiniMorphismSystem.Core.Objects

Identity and composition of functors, plus
morphism system foundations: Iso, MorphismClass,
FactorizationSystem, and LiftingSystem.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Identity Functor -/

def Functor.id (C : Category) : Functor C C where
  mapObj X := X
  mapHom f := f
  preservesId _ := rfl
  preservesComp _ _ := rfl

/-! ## Functor Composition -/

def Functor.comp {C D E : Category} (G : Functor D E) (F : Functor C D) : Functor C E where
  mapObj X := G.mapObj (F.mapObj X)
  mapHom f := G.mapHom (F.mapHom f)
  preservesId X := by
    rw [F.preservesId, G.preservesId]
  preservesComp f g := by
    rw [F.preservesComp, G.preservesComp]

/-! ## Isomorphism in a Category -/

/--
An isomorphism between objects X and Y in a category C:
a pair of morphisms fwd : X → Y, rev : Y → X
that compose to identities both ways.
-/
structure Iso (C : Category) (X Y : C.Obj) where
  fwd : C[X, Y]
  rev : C[Y, X]
  fwd_rev : C.comp fwd rev = C.id Y
  rev_fwd : C.comp rev fwd = C.id X

notation X:50 " ≅ᶜ " Y:50 => Iso _ X Y

/-- Identity isomorphism. -/
def Iso.id (C : Category) (X : C.Obj) : Iso C X X where
  fwd := C.id X
  rev := C.id X
  fwd_rev := C.comp_id (C.id X)
  rev_fwd := C.comp_id (C.id X)

/-- Inverse of an isomorphism. -/
def Iso.symm {C : Category} {X Y : C.Obj} (i : Iso C X Y) : Iso C Y X where
  fwd := i.rev
  rev := i.fwd
  fwd_rev := i.rev_fwd
  rev_fwd := i.fwd_rev

/-- Composition of isomorphisms. -/
def Iso.trans {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (j : Iso C Y Z) : Iso C X Z where
  fwd := C.comp j.fwd i.fwd
  rev := C.comp i.rev j.rev
  fwd_rev := by
    calc
      C.comp (C.comp j.fwd i.fwd) (C.comp i.rev j.rev)
          = C.comp j.fwd (C.comp i.fwd (C.comp i.rev j.rev)) := by
        rw [C.assoc j.fwd i.fwd (C.comp i.rev j.rev)]
      _ = C.comp j.fwd (C.comp (C.comp i.fwd i.rev) j.rev) := by
        rw [← C.assoc i.fwd i.rev j.rev]
      _ = C.comp j.fwd (C.comp (C.id Y) j.rev) := by rw [i.fwd_rev]
      _ = C.comp j.fwd j.rev := by rw [C.id_comp j.rev]
      _ = C.id Z := j.fwd_rev
  rev_fwd := by
    calc
      C.comp (C.comp i.rev j.rev) (C.comp j.fwd i.fwd)
          = C.comp i.rev (C.comp j.rev (C.comp j.fwd i.fwd)) := by
        rw [C.assoc i.rev j.rev (C.comp j.fwd i.fwd)]
      _ = C.comp i.rev (C.comp (C.comp j.rev j.fwd) i.fwd) := by
        rw [← C.assoc j.rev j.fwd i.fwd]
      _ = C.comp i.rev (C.comp (C.id Y) i.fwd) := by rw [j.rev_fwd]
      _ = C.comp i.rev i.fwd := by rw [C.id_comp i.fwd]
      _ = C.id X := i.rev_fwd

/-! ## Morphism Class -/

/--
A morphism class in a category C is a predicate on morphisms.
-/
def MorphismClass (C : Category) : Type (max u (v+1)) :=
  ∀ {X Y : C.Obj}, C[X, Y] → Prop

/-- Test membership in a morphism class. -/
def MorphismClass.mem (M : MorphismClass C) {X Y : C.Obj} (f : C[X, Y]) : Prop := M f

notation f:40 " ∈ₘ " M:40 => MorphismClass.mem M f

/-- A morphism class containing all identity morphisms. -/
def MorphismClass.containsId (M : MorphismClass C) : Prop :=
  ∀ (X : C.Obj), C.id X ∈ₘ M

/-- A morphism class closed under composition with isomorphisms on both sides. -/
def MorphismClass.isoSaturated (M : MorphismClass C) : Prop :=
  ∀ {X Y X' Y' : C.Obj} (i : Iso C X X') (j : Iso C Y Y') (f : C[X, Y]),
    f ∈ₘ M → C.comp j.fwd (C.comp f i.rev) ∈ₘ M

/-! ## Lifting Property -/

/--
e has the left lifting property with respect to m (written e ⋔ m)
if for every commutative square with e on the left and m on the right,
there exists a diagonal filler d.
-/
def HasLLP {C : Category} {A B X Y : C.Obj} (e : C[A, B]) (m : C[X, Y]) : Prop :=
  ∀ (u : C[A, X]) (v : C[B, Y]),
    C.comp m u = C.comp v e →
    ∃ (d : C[B, X]), C.comp d e = u ∧ C.comp m d = v

notation e:40 " ⋔ " m:40 => HasLLP e m

/-- A morphism class E has the left lifting property w.r.t. class M
if every e ∈ E lifts against every m ∈ M. -/
def Orthogonal (E M : MorphismClass C) : Prop :=
  ∀ {A B X Y : C.Obj} (e : C[A, B]) (m : C[X, Y]),
    e ∈ₘ E → m ∈ₘ M → e ⋔ m

notation E:40 " ⊥ " M:40 => Orthogonal E M

/-! ## Factorization System -/

/--
A factorization system (E, M) on a category C consists of:
- two morphism classes E and M
- every morphism f factors as f = m ∘ e with e ∈ E, m ∈ M
- E and M are orthogonal: e ⋔ m for all e ∈ E, m ∈ M
- E and M contain all isomorphisms
-/
structure FactorizationSystem (C : Category) where
  E : MorphismClass C
  M : MorphismClass C
  factorization : ∀ {X Y : C.Obj} (f : C[X, Y]),
    ∃ (Z : C.Obj) (e : C[X, Z]) (m : C[Z, Y]),
      e ∈ₘ E ∧ m ∈ₘ M ∧ C.comp m e = f
  orthogonal : E ⊥ M
  containsIso_e : ∀ {X Y : C.Obj} (i : Iso C X Y), i.fwd ∈ₘ E
  containsIso_m : ∀ {X Y : C.Obj} (i : Iso C X Y), i.fwd ∈ₘ M

/-! ## Lifting System -/

/--
A lifting system is a pair (L, R) of morphism classes such that L ⋔ R.
This is a weaker notion than a factorization system
(no factorization requirement).
-/
structure LiftingSystem (C : Category) where
  L : MorphismClass C
  R : MorphismClass C
  lifting : L ⊥ R

/-- Every factorization system yields a lifting system. -/
def FactorizationSystem.toLiftingSystem {C : Category} (fs : FactorizationSystem C) :
    LiftingSystem C where
  L := fs.E
  R := fs.M
  lifting := fs.orthogonal

#eval "Core.Objects: Functor.id, Functor.comp, Iso, MorphismClass, HasLLP, Orthogonal, FactorizationSystem, LiftingSystem"
#eval "Iso has: fwd, rev, fwd_rev, rev_fwd; supports id, symm, trans"
#eval "FactorizationSystem has: E, M, factorization, orthogonal, containsIso_e, containsIso_m"
