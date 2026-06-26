import Lake
open Lake DSL

package «mini-functor-core» where
  -- Package configuration

@[default_target]
lean_lib «MiniFunctorCore» where
  roots := #[`MiniFunctorCore]

require «mini-category-core» from "../mini-category-core"
require «mini-morphism-system» from "../mini-morphism-system"
