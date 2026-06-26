import Lake
open Lake DSL

package «mini-natural-transformation» where

@[default_target]
lean_lib «MiniNaturalTransformation» where
  roots := #[`MiniNaturalTransformation]

require «mini-category-core» from "../mini-category-core"
require «mini-functor-core» from "../mini-functor-core"
require «mini-morphism-system» from "../mini-morphism-system"
