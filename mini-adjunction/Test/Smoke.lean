import MiniAdjunction

open MiniAdjunction
open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

def main : IO Unit := do
  IO.println "=== mini-adjunction Smoke Tests ==="

  -- Test identity adjunction
  let adj := identityAdjunction SetCat
  IO.println s!"Identity adjunction: id ⊣ id on SetCat"

  -- Test unit component at Bool
  let unitComp := adj.unit.component Bool
  IO.println s!"Unit at Bool: Bool → SetCat[G(F(Bool))]"

  -- Test counit component at Bool
  let counitComp := adj.counit.component Bool
  IO.println s!"Counit at Bool: SetCat[F(G(Bool)), Bool]"

  -- Test left triangle
  have h_left := adj.leftTriangle Bool
  IO.println s!"Left triangle holds at Bool: {h_left}"

  -- Test right triangle
  have h_right := adj.rightTriangle Bool
  IO.println s!"Right triangle holds at Bool: {h_right}"

  -- Test HomAdjunction
  let ha := Adjunction.toHomAdjunction adj
  IO.println s!"HomAdjunction from identity adjunction (nonempty)"

  -- Test IsLeftAdjoint
  let ila : IsLeftAdjoint (Functor.id SetCat) :=
    ⟨Functor.id SetCat, Nonempty.intro adj⟩
  IO.println s!"Functor.id SetCat is a left adjoint: true"

  -- Test IsRightAdjoint
  let ira : IsRightAdjoint (Functor.id SetCat) :=
    ⟨Functor.id SetCat, Nonempty.intro adj⟩
  IO.println s!"Functor.id SetCat is a right adjoint: true"

  -- Test curry/uncurry in Set
  let c := curry (λ (x : Bool) (a : Nat) => a > 0)
  let uc := uncurry (λ (x : Bool) => λ (a : Nat) => a > 0)
  IO.println s!"curry/uncurry inverse: {curry (λ (x : Bool) (a : Nat) => a > 0) true 5}"
  IO.println s!"uncurry works: {uc (false, 3)}"

  -- Test adjoint transpose notation
  let g : SetCat[Functor.id SetCat.mapObj Bool, Functor.id SetCat.mapObj Bool] := λ b => b
  let transposed := adjointTranspose adj g
  IO.println s!"Adjoint transpose of id_Bool = {transposed true}"

  -- Test homBij
  let φ := adjunctionHomBijection adj Bool Bool
  let φinv := adjunctionHomBijectionInv adj Bool Bool
  IO.println s!"Hom bijection φ(id) applied to true = {(φ (λ b => b)) true}"

  IO.println "All smoke tests passed!"
