import Lake
open Lake DSL

package «mini-morphism-system» where

@[default_target]
lean_lib «MiniMorphismSystem» where
  roots := #[`MiniMorphismSystem]

require «mini-category-core» from "../mini-category-core"
require «mini-object-kernel» from "../../0. mini-math-kernel/mini-object-kernel"
