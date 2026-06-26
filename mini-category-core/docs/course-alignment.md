# Course Alignment — mini-category-core

## 9-School Curriculum Mapping

### MIT (18.701/702 Algebra · 18.901 Topology)
| Course Topic | Lean Implementation |
|---|---|
| Category definition | `Core/Basic.lean`: `Category` structure |
| Functors and natural transformations | `Morphisms/Equivalence.lean`: `Functor`, `NatTrans` |
| Limits and colimits | `Theorems/UniversalProperties.lean`: product, coproduct, equalizer, pullback |
| Adjoint functors | `Theorems/UniversalProperties.lean`: `Adjunction` structure |
| Abelian categories | `Bridges/ToAlgebra.lean`: `PreadditiveStructure` |

### Stanford (MATH 205/210 Analysis + Algebra)
| Course Topic | Lean Implementation |
|---|---|
| Categories and functors | `Core/Basic.lean`, `Morphisms/Equivalence.lean` |
| Natural transformations | `Morphisms/Equivalence.lean`: `NatTrans`, vertical composition |
| Yoneda lemma | `Theorems/Main.lean`: stated as axiom |
| Monoidal categories | (gap — not yet implemented) |

### Princeton (MAT 520/560 Complex Analysis + Algebraic Geometry)
| Course Topic | Lean Implementation |
|---|---|
| Sheaves and presheaves | `Morphisms/Equivalence.lean`: `PresheafCategory` |
| Schemes as categories | `Bridges/ToGeometry.lean`: `SchemeCat` |
| Affine schemes = CommRing^op | `Bridges/ToGeometry.lean`: axiom |

### Berkeley (MATH 250A Algebra · 202A Topology)
| Course Topic | Lean Implementation |
|---|---|
| Category theory fundamentals | Full coverage across Core/Morphisms/Constructions |
| Homological algebra | `Bridges/ToAlgebra.lean`: preadditive structure |
| Topological categories | `Bridges/ToTopology.lean`: TopCategory, fundamental groupoid |

### Cambridge (Part III)
| Course Topic | Lean Implementation |
|---|---|
| Categories, functors, natural transformations | Full coverage |
| Limits, colimits, adjunctions | `Theorems/UniversalProperties.lean` |
| Monads and algebras | `Bridges/ToComputation.lean`: `Monad` structure |
| Abelian and derived categories | (partially: preadditive structure) |

### Oxford (B4 Functional Analysis · C2 Category Theory · C3 Algebraic Topology)
| Course Topic | Lean Implementation |
|---|---|
| Category theory core | Full: categories through adjunctions |
| Topos theory | `Bridges/ToGeometry.lean`: `GeometricMorphism`, `ToposCat` |
| Homotopy theory | `Bridges/ToTopology.lean`: `HomotopyCategory` |

### ETH (401-3001 Algebra I/II · 401-3462 Functional Analysis)
| Course Topic | Lean Implementation |
|---|---|
| Algebraic structures | `Bridges/ToAlgebra.lean`: monoids, groups, rings as categories |
| Category theory | Full coverage across all modules |

### ENS (Analysis on Manifolds · Algebraic Topology · Commutative Algebra)
| Course Topic | Lean Implementation |
|---|---|
| Bourbaki structural approach | Theory registration via `MiniObjectKernel` |
| Categories and topoi | `Bridges/ToGeometry.lean`: geometric morphisms |
| Homological algebra | `Bridges/ToAlgebra.lean`: preadditive structure |

### 清华 (抽象代数 · 实分析与泛函 · 代数拓扑 · 代数几何)
| Course Topic | Lean Implementation |
|---|---|
| Abstract algebra via categories | `Bridges/ToAlgebra.lean`: groups, rings as categories |
| Category theory fundamentals | Full coverage |
| Algebraic geometry basics | `Bridges/ToGeometry.lean`: schemes, topoi |
