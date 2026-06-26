import Lake
open Lake DSL

package «mini-yoneda-lite» where

@[default_target]
lean_lib «MiniYonedaLite» where
  roots := #[`MiniYonedaLite]

require «mini-category-core» from "../mini-category-core"
require «mini-functor-core» from "../mini-functor-core"
require «mini-natural-transformation» from "../mini-natural-transformation"
