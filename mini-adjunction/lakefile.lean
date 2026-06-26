import Lake
open Lake DSL

package «mini-adjunction» where

@[default_target]
lean_lib «MiniAdjunction» where
  roots := #[`MiniAdjunction]

require «mini-category-core» from "../mini-category-core"
require «mini-functor-core» from "../mini-functor-core"
require «mini-natural-transformation» from "../mini-natural-transformation"
