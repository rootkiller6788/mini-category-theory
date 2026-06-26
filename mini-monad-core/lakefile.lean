import Lake
open Lake DSL

package «mini-monad-core» where

@[default_target]
lean_lib «MiniMonadCore» where
  roots := #[`MiniMonadCore]

require «mini-category-core» from "../mini-category-core"
require «mini-functor-core» from "../mini-functor-core"
require «mini-natural-transformation» from "../mini-natural-transformation"
require «mini-adjunction» from "../mini-adjunction"
