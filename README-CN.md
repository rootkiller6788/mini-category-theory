# Mini Category Theory（迷你范畴论）

一套**从零开始、零依赖的 Lean 4 实现**，涵盖大学层次的范畴论与函子数学。每个子包对应 MIT（及其他顶尖大学）课程，使用 Lean 4 证明助手从第一性原理构建范畴论基础。

## 子包

| 子包 | 主题 | 核心课程 |
|------|------|----------|
| [mini-category-core](mini-category-core/) | 范畴、对象、态射、对偶范畴、积 | MIT 18.996, Cambridge Part III |
| [mini-functor-core](mini-functor-core/) | 函子、函子范畴、切片/逗号范畴 | MIT 18.996, Princeton MAT 595 |
| [mini-natural-transformation](mini-natural-transformation/) | 自然变换、自然同构、函子范畴 | MIT 18.996, Harvard Math 254 |
| [mini-adjunction](mini-adjunction/) | 伴随函子、单位/余单位、自由/遗忘、Galois 联络 | MIT 18.996, Cambridge Part III |
| [mini-limit-colimit](mini-limit-colimit/) | 极限、余极限、等化子、拉回、完备性 | MIT 18.996, Princeton MAT 595 |
| [mini-monad-core](mini-monad-core/) | 单子、Kleisli 三元组、代数、单子变换器 | MIT 6.821, Oxford CS |
| [mini-morphism-system](mini-morphism-system/) | 分解系统、(E,M)-分解、提升性质 | MIT 18.996, Cambridge Part III |
| [mini-yoneda-lite](mini-yoneda-lite/) | Yoneda 引理、可表函子、万有元素 | MIT 18.996, Princeton MAT 595 |

## 设计理念

- **零外部依赖** -- 纯 Lean 4，仅导入内核模块
- **自包含子包** -- 每个子包拥有独立的 `lakefile.lean`、Core/、Morphisms/、Constructions/、Properties/、Theorems/
- **理论到代码的映射** -- 每个模块包含内联 `#eval` 示例和定理陈述
- **宇宙多态** -- 范畴使用 `Obj : Type u` 和 `Hom : Obj -> Obj -> Type v` 实现灵活的宇宙层级处理

## 构建

每个子包独立构建。使用 Lake 构建：

```bash
cd mini-category-core
lake build
lake env lean --run Test/Smoke.lean
```

需要 **Lean 4** 和 **Lake**。

## 项目结构

```
2. mini-category-theory/
├── mini-category-core/              # 范畴、对象、态射、积
├── mini-functor-core/               # 函子、函子范畴、切片/逗号范畴
├── mini-natural-transformation/     # 自然变换、同构
├── mini-adjunction/                 # 伴随函子、单位/余单位、Galois 联络
├── mini-limit-colimit/              # 极限、余极限、等化子、拉回
├── mini-monad-core/                 # 单子、Kleisli 三元组、代数
├── mini-morphism-system/            # 分解系统、提升性质
├── mini-yoneda-lite/                # Yoneda 引理、可表函子
└── lakefile.lean
```

## 许可证

MIT
