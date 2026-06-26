import Lake
open Lake DSL

package «mini-category-core» where
  -- Core category theory package

@[default_target]
lean_lib «MiniCategoryCore» where
  roots := #[`MiniCategoryCore]
  defaultFacets := #[ModuleFacet.oleans]

require «mini-object-kernel» from "../../0. mini-math-kernel/mini-object-kernel"
