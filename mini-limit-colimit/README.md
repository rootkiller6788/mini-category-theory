# mini-limit-colimit

Limits and colimits in category theory: diagrams, cones, cocones, universal properties,
products, coproducts, complete/cocomplete categories.

## Contents

- `Core/Basic.lean` -- Diagram, Cone, Cocone, ConeCat
- `Core/Objects.lean` -- Limit, Colimit structures (terminal/initial in cone categories)
- `Core/Laws.lean` -- Limit/colimit uniqueness laws
- `Constructions/Products.lean` -- Product and coproduct as limits/colimits over discrete diagrams
- `Constructions/Universal.lean` -- IsComplete, IsCocomplete, empty diagram limits

## Dependencies

- `mini-category-core` (Category, SetCat, functor)
- `mini-functor-core` (Functor, diagram as functor)
- `mini-natural-transformation` (morphisms of diagrams)
