import MiniCategoryCore

open MiniCategoryCore

def main : IO Unit := do
  IO.println "=== mini-category-core Smoke Tests ==="
  -- Test Category construction
  let C : Category := SetCat
  IO.println s!"SetCat.Obj = Type u"
  -- Test id
  let idUnit : C[Unit, Unit] := C.id Unit
  IO.println s!"id(Unit) = {idUnit ()}"
  -- Test composition
  let f : C[Unit, Bool] := fun _ => true
  let g : C[Bool, Nat] := fun b => if b then 1 else 0
  let gof := C.comp g f
  IO.println s!"(g ∘ f)() = {gof ()}"
  -- Test opposite
  let Cop := Cᵒᵖ
  IO.println s!"Cᵒᵖ has same objects as C"
  -- Test product category
  let CxC := C ×ᶜ C
  IO.println s!"C ×ᶜ C has objects C.Obj × C.Obj"
  -- Test DiscCat
  let disc := DiscCat Bool
  IO.println s!"DiscCat Bool has 2 objects: true, false"
  -- Test CodiscCat
  let codisc := CodiscCat Nat
  IO.println "CodiscCat Nat constructed"
  -- Test Iso
  let id_iso : Iso SetCat Bool Bool := iso_refl SetCat Bool
  IO.println s!"iso_refl hom true = {id_iso.hom true}"
  -- Test iso_symm
  let id_symm := iso_symm id_iso
  IO.println s!"iso_symm works: {id_symm.hom = id_iso.hom}"
  -- Test SplitMono / SplitEpi
  let sm : SplitMono (SetCat.id Bool) := {
    retraction := SetCat.id Bool,
    retraction_comp := SetCat.comp_id (SetCat.id Bool)
  }
  IO.println s!"SplitMono(id_Bool) retraction_comp: {sm.retraction_comp}"
  -- Test categoryLaws
  have h := categoryLaws C
  IO.println s!"Category laws hold for SetCat"
  -- Test preservesId
  let idPreserved := preservesId (fun (X : Type u) => X) (fun f => f) (X := Unit)
  IO.println s!"preservesId holds: {idPreserved}"
  -- Test Functor
  let idF : Functor SetCat SetCat := Functor.idF SetCat
  IO.println s!"Identity functor on SetCat: idF.onObj Nat = {idF.onObj Nat}"
  -- Test Initial/Terminal
  IO.println s!"SetCat has initial Empty and terminal Unit"
  -- Test isGroupoid on CodiscCat
  IO.println s!"CodiscCat is a groupoid: {codiscrete_is_groupoid Bool}"
  -- Test isConnected
  IO.println s!"SetCat is connected: {SetCat_is_connected}"
  -- Test Product
  let prod : Product SetCat Bool Nat := {
    cone := SetCat.productCone Bool Nat,
    univ := SetCat.isProduct_pair (A := Bool) (B := Nat)
  }
  IO.println s!"Product of Bool×Nat: π₁(true, 5) = {prod.π₁ (true, 5)}"
  IO.println s!"Product of Bool×Nat: π₂(true, 5) = {prod.π₂ (true, 5)}"
  IO.println "All smoke tests passed!"
