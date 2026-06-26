import Lake
open Lake DSL

package «mini-limit-colimit» where

@[default_target]
lean_lib «MiniLimitColimit» where
  roots := #[`MiniLimitColimit]

require «mini-category-core» from "../mini-category-core"
require «mini-functor-core» from "../mini-functor-core"
require «mini-natural-transformation» from "../mini-natural-transformation"
