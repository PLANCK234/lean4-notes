## 高斯消元代码阅读

### 矩阵

以类型 m 为行索引、类型 n 为列索引、元素类型为 α

阿尔法代表的是元素类型


`Matrix (Fin m) (Fin n) α`：m是行，n是列
`Matrix.transpose`：矩阵的转置
`Matrix.submatrix`: take a submatrix by reindexing rows and columns 我们是改变m，n的指标来对一个矩阵进行初等变换
`Matrix.module`: matrices are a module over the ring of entries

```lean
#eval !![1, 1; 1, 1]   -- notation sugar for Matrix (Fin 2) (Fin 2) ℤ
```


- exact 在tacitic环境中开一个短暂的term mode 环境

\^T 代表转置， \^H 共轭转置（conjugate transpose，或 Hermitian transpose）

| Typeclass | 用途                           | 示例类型              |
| --------- | ---------------------------- | ----------------- |
| `Star`    | 表示可以取“共轭”的结构                 | 复数、矩阵、Hilbert 空间  |
| `Algebra` | 表示代数结构（模 + 环 + `algebraMap`） | ℝ → ℂ，ℚ → ℝ，多项式环等 |

| 对象类型         | `star` 操作代表    | 示例                              |
| ------------ | -------------- | ------------------------------- |
| 复数 `ℂ`       | 复共轭            | `star (3 + 4i) = 3 - 4i`        |
| 复矩阵          | 共轭转置           | `star A = A† = (Aᵀ)̄`           |
| Hilbert 空间向量 | 线性对偶 / adjoint | `⟨x, y⟩ = ⟨y, x⟩̄`              |
| \*-代数元素      | 星代数 involution | `star(a * b) = star b * star a` |





