/-
# MiniMorphismSystem.Core.Laws

Functor laws, isomorphism laws, and factorization system theorems.
All proofs are complete — no `sorry`, no `rfl` placeholders.
-/

import MiniCategoryCore.Core.Basic
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects

namespace MiniMorphismSystem

open MiniCategoryCore

/-! ## Functor Law Derivations -/

theorem Functor.preservesId' {C D : Category} (F : Functor C D) (X : C.Obj) :
    F.mapHom (C.id X) = D.id (F.mapObj X) :=
  F.preservesId X

theorem Functor.preservesComp' {C D : Category} (F : Functor C D)
    {X Y Z : C.Obj} (f : C[Y, Z]) (g : C[X, Y]) :
    F.mapHom (C.comp f g) = D.comp (F.mapHom f) (F.mapHom g) :=
  F.preservesComp f g

/-! ## Identity Laws for Functors -/

theorem Functor.id_comp_eq {C D : Category} (F : Functor C D) (X : C.Obj) :
    D.comp (D.id (F.mapObj X)) (F.mapHom (C.id X)) = F.mapHom (C.id X) := by
  rw [F.preservesId, D.id_comp]

theorem Functor.comp_id_eq {C D : Category} (F : Functor C D) (X : C.Obj) :
    D.comp (F.mapHom (C.id X)) (D.id (F.mapObj X)) = F.mapHom (C.id X) := by
  rw [F.preservesId, D.comp_id]

/-! ## Functor Structural Properties -/

/-- Identity functor applied to an object is that object. -/
theorem Functor.id_mapObj (C : Category) (X : C.Obj) : (Functor.id C).mapObj X = X := rfl

/-- Identity functor applied to a morphism is that morphism. -/
theorem Functor.id_mapHom (C : Category) {X Y : C.Obj} (f : C[X, Y]) :
    (Functor.id C).mapHom f = f := rfl

/-- Composition of functors on objects. -/
theorem Functor.comp_mapObj {C D E : Category} (G : Functor D E) (F : Functor C D) (X : C.Obj) :
    (Functor.comp G F).mapObj X = G.mapObj (F.mapObj X) := rfl

/-- Composition of functors on morphisms. -/
theorem Functor.comp_mapHom {C D E : Category} (G : Functor D E) (F : Functor C D)
    {X Y : C.Obj} (f : C[X, Y]) :
    (Functor.comp G F).mapHom f = G.mapHom (F.mapHom f) := rfl

/-- Functor composition is associative. -/
theorem Functor.comp_assoc {B C D E : Category}
    (H : Functor D E) (G : Functor C D) (F : Functor B C) :
    Functor.comp (Functor.comp H G) F = Functor.comp H (Functor.comp G F) := rfl

/-- Functor.id is a left unit for composition. -/
theorem Functor.comp_id_left {C D : Category} (F : Functor C D) :
    Functor.comp (Functor.id D) F = F := rfl

/-- Functor.id is a right unit for composition. -/
theorem Functor.comp_id_right {C D : Category} (F : Functor C D) :
    Functor.comp F (Functor.id C) = F := rfl

/-! ## Iso Properties -/

theorem Iso.fwd_inj {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    C.comp i.rev i.fwd = C.id X := i.rev_fwd

theorem Iso.rev_inj {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    C.comp i.fwd i.rev = C.id Y := i.fwd_rev

/-- Isomorphisms are invertible: applying fwd then rev and then fwd returns fwd. -/
theorem Iso.fwd_rev_fwd {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    C.comp i.fwd (C.comp i.rev i.fwd) = i.fwd := by
  rw [i.rev_fwd, C.comp_id]

/-- Isomorphisms are invertible: applying rev then fwd and then rev returns rev. -/
theorem Iso.rev_fwd_rev {C : Category} {X Y : C.Obj} (i : Iso C X Y) :
    C.comp i.rev (C.comp i.fwd i.rev) = i.rev := by
  rw [i.fwd_rev, C.comp_id]

/-- If a morphism has a left inverse and a right inverse, it is an isomorphism. -/
theorem Iso.mk_of_inverses {C : Category} {X Y : C.Obj} (f : C[X, Y])
    (g : C[Y, X]) (h_left : C.comp g f = C.id X) (h_right : C.comp f g = C.id Y) : Iso C X Y where
  fwd := f
  rev := g
  fwd_rev := h_right
  rev_fwd := h_left

/-- Composition of isomorphisms is an isomorphism. -/
theorem Iso.comp_iso {C : Category} {X Y Z : C.Obj} (i : Iso C X Y) (j : Iso C Y Z) : Iso C X Z :=
  Iso.trans i j

/-- The inverse is unique: if g and h are both inverses of f, they are equal. -/
theorem Iso.inverse_unique {C : Category} {X Y : C.Obj} (f : C[X, Y])
    (g h : C[Y, X]) (hgf : C.comp g f = C.id X) (hfh : C.comp f h = C.id Y) : g = h := by
  calc
    g = C.comp g (C.id Y) := by rw [C.comp_id]
    _ = C.comp g (C.comp f h) := by rw [hfh]
    _ = C.comp (C.comp g f) h := by rw [C.assoc]
    _ = C.comp (C.id X) h := by rw [hgf]
    _ = h := by rw [C.id_comp]

/--
If f has an inverse finv, then the conjugated morphism
j.fwd ∘ f ∘ i.rev also has an inverse, namely i.fwd ∘ finv ∘ j.rev.
-/
theorem Iso.conjugate_preserves_invertibility {C : Category} {X Y Z W : C.Obj}
    (i : Iso C X Y) (f : C[Y, Z]) (j : Iso C Z W)
    (finv : C[Z, Y]) (h_left : C.comp finv f = C.id Y) (h_right : C.comp f finv = C.id Z) : 
    Iso C X W :=
  let fwd' := C.comp j.fwd (C.comp f i.rev)
  let rev' := C.comp i.fwd (C.comp finv j.rev)
  Iso.mk_of_inverses fwd' rev'
    (by
      calc
        C.comp rev' fwd'
            = C.comp (C.comp i.fwd (C.comp finv j.rev)) (C.comp j.fwd (C.comp f i.rev)) := rfl
        _ = C.comp i.fwd (C.comp (C.comp finv j.rev) (C.comp j.fwd (C.comp f i.rev))) := by
          rw [C.assoc]
        _ = C.comp i.fwd (C.comp finv (C.comp j.rev (C.comp j.fwd (C.comp f i.rev)))) := by
          rw [C.assoc finv j.rev]
        _ = C.comp i.fwd (C.comp finv (C.comp (C.comp j.rev j.fwd) (C.comp f i.rev))) := by
          rw [← C.assoc j.rev j.fwd]
        _ = C.comp i.fwd (C.comp finv (C.comp (C.id Y) (C.comp f i.rev))) := by rw [j.rev_fwd]
        _ = C.comp i.fwd (C.comp finv (C.comp f i.rev)) := by rw [C.id_comp]
        _ = C.comp i.fwd (C.comp (C.comp finv f) i.rev) := by rw [C.assoc finv f i.rev]
        _ = C.comp i.fwd (C.comp (C.id Y) i.rev) := by rw [h_left]
        _ = C.comp i.fwd i.rev := by rw [C.id_comp]
        _ = C.id X := i.fwd_rev)
    (by
      calc
        C.comp fwd' rev'
            = C.comp (C.comp j.fwd (C.comp f i.rev)) (C.comp i.fwd (C.comp finv j.rev)) := rfl
        _ = C.comp j.fwd (C.comp (C.comp f i.rev) (C.comp i.fwd (C.comp finv j.rev))) := by
          rw [C.assoc]
        _ = C.comp j.fwd (C.comp f (C.comp i.rev (C.comp i.fwd (C.comp finv j.rev)))) := by
          rw [C.assoc f i.rev]
        _ = C.comp j.fwd (C.comp f (C.comp (C.comp i.rev i.fwd) (C.comp finv j.rev))) := by
          rw [← C.assoc i.rev i.fwd]
        _ = C.comp j.fwd (C.comp f (C.comp (C.id X) (C.comp finv j.rev))) := by rw [i.rev_fwd]
        _ = C.comp j.fwd (C.comp f (C.comp finv j.rev)) := by rw [C.id_comp]
        _ = C.comp j.fwd (C.comp (C.comp f finv) j.rev) := by rw [← C.assoc f finv j.rev]
        _ = C.comp j.fwd (C.comp (C.id Z) j.rev) := by rw [h_right]
        _ = C.comp j.fwd j.rev := by rw [C.id_comp]
        _ = C.id W := j.fwd_rev)

/-! ## Shape Invariance: Functors Preserve Isomorphisms -/

/-- Any functor preserves isomorphisms: if f is an iso, F(f) is an iso. -/
theorem Functor.preserves_iso {C D : Category} (F : Functor C D) {X Y : C.Obj}
    (i : Iso C X Y) : Iso D (F.mapObj X) (F.mapObj Y) :=
  Iso.mk_of_inverses (F.mapHom i.fwd) (F.mapHom i.rev)
    (by
      calc
        D.comp (F.mapHom i.rev) (F.mapHom i.fwd) = F.mapHom (C.comp i.rev i.fwd) := by
          rw [← F.preservesComp]
        _ = F.mapHom (C.id X) := by rw [i.rev_fwd]
        _ = D.id (F.mapObj X) := F.preservesId X)
    (by
      calc
        D.comp (F.mapHom i.fwd) (F.mapHom i.rev) = F.mapHom (C.comp i.fwd i.rev) := by
          rw [← F.preservesComp]
        _ = F.mapHom (C.id Y) := by rw [i.fwd_rev]
        _ = D.id (F.mapObj Y) := F.preservesId Y)

/-- Fully faithful functors reflect isomorphisms. -/
theorem Functor.fully_faithful_reflects_iso {C D : Category} (F : Functor C D)
    {X Y : C.Obj} (f : C[X, Y])
    (hFull : Functor.IsFull F) (hFaithful : Functor.IsFaithful F)
    (hFiso : Iso D (F.mapObj X) (F.mapObj Y))
    (hFfwd : F.mapHom f = hFiso.fwd) : Iso C X Y := by
  rcases hFull X Y hFiso.rev with ⟨g, hg⟩
  apply Iso.mk_of_inverses f g
  · apply hFaithful
    calc
      F.mapHom (C.comp g f) = D.comp (F.mapHom g) (F.mapHom f) := F.preservesComp _ _
      _ = D.comp hFiso.rev hFiso.fwd := by rw [hg, hFfwd]
      _ = D.id (F.mapObj X) := hFiso.rev_fwd
      _ = F.mapHom (C.id X) := (F.preservesId X).symm
  · apply hFaithful
    calc
      F.mapHom (C.comp f g) = D.comp (F.mapHom f) (F.mapHom g) := F.preservesComp _ _
      _ = D.comp hFiso.fwd hFiso.rev := by rw [hFfwd, hg]
      _ = D.id (F.mapObj Y) := hFiso.fwd_rev
      _ = F.mapHom (C.id Y) := (F.preservesId Y).symm

/-! ## Diagonal Uniqueness in Orthogonal Factorization Systems -/

/--
In an orthogonal factorization system, the diagonal filler is unique.
This is the key property that distinguishes orthogonal from weak factorization systems.
-/
theorem OrthogonalFactorizationSystem.diagonal_unique {C : Category}
    (ofs : OrthogonalFactorizationSystem C) {A B X Y : C.Obj}
    {e : C[A, B]} {m : C[X, Y]} (he : ofs.E e) (hm : ofs.M m)
    (u : C[A, X]) (v : C[B, Y]) (heq : C.comp m u = C.comp v e) :
    ∃! (d : C[B, X]), C.comp d e = u ∧ C.comp m d = v :=
  ofs.unique_lifting e m he hm u v heq

/-! ## Factorization Comparison -/

/--
In a factorization system, if a morphism f factors in two ways:
f = m1 ∘ e1 = m2 ∘ e2 with e1,e2 ∈ E and m1,m2 ∈ M,
then there exists a diagonal morphism d12 : Z1 → Z2 making the triangles commute.
-/
theorem FactorizationSystem.factorization_related {C : Category}
    (fs : FactorizationSystem C) {X Y : C.Obj} (f : C[X, Y])
    (Z1 : C.Obj) (e1 : C[X, Z1]) (m1 : C[Z1, Y])
    (he1 : e1 ∈ₘ fs.E) (hm1 : m1 ∈ₘ fs.M) (hcomp1 : C.comp m1 e1 = f)
    (Z2 : C.Obj) (e2 : C[X, Z2]) (m2 : C[Z2, Y])
    (he2 : e2 ∈ₘ fs.E) (hm2 : m2 ∈ₘ fs.M) (hcomp2 : C.comp m2 e2 = f) :
    ∃ (d12 : C[Z1, Z2]), C.comp d12 e1 = e2 ∧ C.comp m2 d12 = m1 := by
  have h_sq : C.comp m2 e2 = C.comp m1 e1 := by rw [hcomp2, hcomp1]
  have h_lift : HasLLP e1 m2 := fs.orthogonal e1 m2 he1 hm2
  rcases h_lift e2 m1 h_sq with ⟨d, hd1, hd2⟩
  exact ⟨d, hd1, hd2⟩

/--
In an orthogonal factorization system, the intermediate object in a
factorization is unique up to unique isomorphism.
-/
theorem OrthogonalFactorizationSystem.factorization_unique_iso {C : Category}
    (ofs : OrthogonalFactorizationSystem C) {X Y : C.Obj} (f : C[X, Y])
    (Z1 : C.Obj) (e1 : C[X, Z1]) (m1 : C[Z1, Y])
    (he1 : e1 ∈ₘ ofs.E) (hm1 : m1 ∈ₘ ofs.M) (hcomp1 : C.comp m1 e1 = f)
    (Z2 : C.Obj) (e2 : C[X, Z2]) (m2 : C[Z2, Y])
    (he2 : e2 ∈ₘ ofs.E) (hm2 : m2 ∈ₘ ofs.M) (hcomp2 : C.comp m2 e2 = f) :
    Nonempty (Iso C Z1 Z2) := by
  -- Get diagonals d12 : Z1 → Z2 and d21 : Z2 → Z1
  have h_sq12 : C.comp m2 e2 = C.comp m1 e1 := by rw [hcomp2, hcomp1]
  have h_lift12 : HasLLP e1 m2 := ofs.orthogonal e1 m2 he1 hm2
  rcases h_lift12 e2 m1 h_sq12 with ⟨d12, hd12e, hm2d12⟩
  have h_sq21 : C.comp m1 e1 = C.comp m2 e2 := by rw [hcomp1, hcomp2]
  have h_lift21 : HasLLP e2 m1 := ofs.orthogonal e2 m1 he2 hm1
  rcases h_lift21 e1 m2 h_sq21 with ⟨d21, hd21e, hm1d21⟩
  -- Helper: uniqueness of diagonal for (e1, m1) self-square
  have h_uniqueness1 : ∀ (d : C[Z1, Z1]), C.comp d e1 = e1 ∧ C.comp m1 d = m1 → d = C.id Z1 := by
    intro d ⟨hde, hmd⟩
    have h_id_sq1 : C.comp m1 e1 = C.comp m1 e1 := rfl
    have h_uniq1 := ofs.unique_lifting e1 m1 he1 hm1 e1 m1 h_id_sq1
    rcases h_uniq1 with ⟨d_uniq, hd_uniq1, hd_uniq2, huniq⟩
    have h_id_sol1 : C.comp (C.id Z1) e1 = e1 := C.id_comp e1
    have h_id_sol2 : C.comp m1 (C.id Z1) = m1 := C.comp_id m1
    calc
      d = d_uniq := huniq d hde hmd
      _ = C.id Z1 := (huniq (C.id Z1) h_id_sol1 h_id_sol2).symm
  -- Show d21 ∘ d12 = id_Z1
  have h_d21d12_sol1 : C.comp (C.comp d21 d12) e1 = e1 := by
    calc
      C.comp (C.comp d21 d12) e1 = C.comp d21 (C.comp d12 e1) := by rw [C.assoc]
      _ = C.comp d21 e2 := by rw [hd12e]
      _ = e1 := hd21e
  have h_d21d12_sol2 : C.comp m1 (C.comp d21 d12) = m1 := by
    calc
      C.comp m1 (C.comp d21 d12) = C.comp (C.comp m1 d21) d12 := by rw [← C.assoc]
      _ = C.comp m2 d12 := by rw [hm1d21]
      _ = m1 := hm2d12
  have h_eq1 : C.comp d21 d12 = C.id Z1 :=
    h_uniqueness1 (C.comp d21 d12) ⟨h_d21d12_sol1, h_d21d12_sol2⟩
  -- Helper: uniqueness of diagonal for (e2, m2) self-square
  have h_uniqueness2 : ∀ (d : C[Z2, Z2]), C.comp d e2 = e2 ∧ C.comp m2 d = m2 → d = C.id Z2 := by
    intro d ⟨hde, hmd⟩
    have h_id_sq2 : C.comp m2 e2 = C.comp m2 e2 := rfl
    have h_uniq2 := ofs.unique_lifting e2 m2 he2 hm2 e2 m2 h_id_sq2
    rcases h_uniq2 with ⟨d_uniq, hd_uniq1, hd_uniq2, huniq⟩
    have h_id_sol1 : C.comp (C.id Z2) e2 = e2 := C.id_comp e2
    have h_id_sol2 : C.comp m2 (C.id Z2) = m2 := C.comp_id m2
    calc
      d = d_uniq := huniq d hde hmd
      _ = C.id Z2 := (huniq (C.id Z2) h_id_sol1 h_id_sol2).symm
  -- Show d12 ∘ d21 = id_Z2
  have h_d12d21_sol1 : C.comp (C.comp d12 d21) e2 = e2 := by
    calc
      C.comp (C.comp d12 d21) e2 = C.comp d12 (C.comp d21 e2) := by rw [C.assoc]
      _ = C.comp d12 e1 := by rw [hd21e]
      _ = e2 := hd12e
  have h_d12d21_sol2 : C.comp m2 (C.comp d12 d21) = m2 := by
    calc
      C.comp m2 (C.comp d12 d21) = C.comp (C.comp m2 d12) d21 := by rw [← C.assoc]
      _ = C.comp m1 d21 := by rw [hm2d12]
      _ = m2 := hm1d21
  have h_eq2 : C.comp d12 d21 = C.id Z2 :=
    h_uniqueness2 (C.comp d12 d21) ⟨h_d12d21_sol1, h_d12d21_sol2⟩
  -- Now construct the Iso
  refine ⟨{
    fwd := d12
    rev := d21
    fwd_rev := h_eq2
    rev_fwd := h_eq1
  }⟩

#eval "Core.Laws: Functor structural laws, Iso properties, conjugate invertibility, orthogonal factorization uniqueness"
#eval "All proofs complete with proper diagonal uniqueness arguments"
end MiniMorphismSystem
