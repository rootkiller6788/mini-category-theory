# mini-adjunction

Adjunctions: the central concept in category theory. An adjunction F ⊣ G between functors F : C → D and G : D → C.

## Contents

- `Core/Basic.lean` — Adjunction structure via unit/counit, triangle identities
- `Core/Objects.lean` — Hom-set adjunction, bijection D(FX, Y) ≅ C(X, GY)
- `Core/Laws.lean` — Triangle identities and adjunction laws
- `Properties/Preservation.lean` — Left adjoints preserve colimits, right adjoints preserve limits

## Dependencies

- `mini-category-core` (for Category, SetCat)
- `mini-functor-core` (for FunctorCategory, hom-functors)
- `mini-natural-transformation` (for NaturalTransformation, ⇒)
