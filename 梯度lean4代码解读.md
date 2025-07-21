# Lean4 中 Hilbert 空间函数梯度的定义和定理解读

下面我们通过 **Lean4** 代码结合自然语言解释，详细介绍 Hilbert 空间中函数梯度（*Gradient*）的定义和性质。为了便于理解，我们将先给出 Lean4 原始代码片段，然后在其后提供通俗易懂的解释，包括严谨的数学定义和公式。

## 背景和主要内容

Lean4 代码中首先导入了一些需要的数学库，然后通过文档注释（`/-! ... -/`）概述了本文件的主要定义和结论。以下是代码的开头部分：

```lean
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`), `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file contains the following parts of gradient.
* the definition of gradient.
* the theorems translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `Gradient` and `fderiv`.
* theorems the Uniqueness of Gradient.
* the theorems translating between  `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `Gradient` and `deriv` when `F = 𝕜`.
* the theorems about the congruence of the gradient.
* the theorems about the gradient of constant function.
* the theorems about the continuity of a function admitting a gradient.
-/
```

\*\*解释：\*\*上述代码导入了 Hilbert 空间对偶、微分（Fréchet 导数 `fderiv` 和常规导数 `deriv`）等模块，然后通过注释说明了本文件的内容：

* **梯度的主要定义（Main Definitions）**：定义 Hilbert 空间中函数的梯度概念。其中 `HasGradientWithinAt f f' s x` 表示函数 `f: F → 𝕜`（其中 `F` 是 Hilbert 空间，`𝕜` 是实数 `ℝ` 或复数 `ℂ`）在点 `x ∈ F` 处（相对于集合 `s` 的限制）具有梯度 `f'`。如果不用子集限制（即整个空间），则记作 `HasGradientAt f f' x`，相当于 `s = univ`（整个空间）。

* **主要结论（Main results）**：包括以下几个部分：

  1. 梯度定义本身，以及与 Fréchet 导数 (`fderiv`) 之间的等价关系（`HasGradientAtFilter` ↔ `HasFDerivAtFilter`，`HasGradientWithinAt` ↔ `HasFDerivWithinAt`，等等）。
  2. 梯度唯一性的定理（梯度在存在时是唯一的）。
  3. 当自变量空间 `F = 𝕜`（一维情形）时，梯度与常规导数的关系（`HasGradientAt` ↔ `HasDerivAt`，以及梯度值等于导数值）。
  4. 梯度在函数相等或限制改变时的“一致性”性质（congruence properties）。
  5. 常数函数的梯度性质（应为零）。
  6. 若函数存在梯度，则函数在该点是连续的等性质。

在下面的内容中，我们将逐步分析代码，解释这些定义和定理的含义。

## 梯度的定义 (Gradient Definitions)

首先，代码中对梯度作了形式化定义。这些定义建立在 Hilbert 空间的内积结构上，使得我们可以利用 Riesz 表示定理将线性泛函对应到梯度向量。让我们看代码：

```lean
open Topology InnerProductSpace Function Set

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x : F}

/-- A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', x' - x⟫ + o (x' - x)` when `x'` converges along the filter `L`. -/
def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') x L

/-- `f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', x' - x⟫ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)

/-- `f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', x' - x⟫ + o (x' - x)` where `x'` converges to `x`. -/
def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)
```

**解释：**这段代码定义了**梯度存在**的几个概念：

* \*\*`HasGradientAtFilter f f' x L`：\*\*定义 `f` 在点 `x` 处沿过滤器 `L` 有梯度 `f'`。形式上，这意味着当 `x'` 沿着过滤器 `L` 趋于 `x` 时，有：
  $f(x') = f(x) + \langle f',\, x' - x\rangle + o(\|x' - x\|),$
  也就是说，\$f(x') - f(x) - \langle f', x'-x\rangle\$ 是比 \$|x'-x|\$ 高阶的小量（\$o(x'-x)\$）。这里 \$\langle f', x' - x\rangle\$ 表示 Hilbert 空间中的内积 \$\langle f', x'-x\rangle\$，`toDual 𝕜 F f'` 是通过内积将向量 `f'` 转换为对应的连续线性泛函（Fréchet 导数），`HasFDerivAtFilter` 则是 Lean4 中 **Fréchet 导数存在** 的定义。在 Hilbert 空间中，Fréchet 导数可以用某个向量的内积来表示，这个向量就是我们定义的梯度 `f'`。

* \*\*`HasGradientWithinAt f f' s x`：\*\*定义 `f` 在点 `x` 处相对于子集 `s` 有梯度 `f'`。这等价于说，当 \$x' \to x\$ 且 \$x' \in s\$ 时，上述梯度关系成立。Lean4 使用 `𝓝[s] x` 表示在 \$x\$ 点相对于集合 \$s\$ 的邻域过滤器。换言之，如果我们只考虑 \$x'\$ 在 \$s\$ 内趋于 \$x\$，\$f(x')\$ 的变化满足 \$f(x') = f(x) + \langle f', x'-x\rangle + o(|x'-x|)\$。

* \*\*`HasGradientAt f f' x`：\*\*定义 `f` 在点 `x` 处（全空间上）有梯度 `f'`，也就是当 \$x' \to x\$ 时，全局的梯度关系成立。Lean4 代码里将其定义为 `HasGradientAtFilter f f' x (𝓝 x)`，相当于 \$L\$ 取为 \$\mathcal{N}(x)\$（\$x\$ 的邻域过滤器，不限制在某个子集）。

换句话说，这三个定义彼此相关：
`HasGradientAt` 是 `HasGradientAtFilter` 在标准邻域过滤器下的特例；
`HasGradientWithinAt` 则是限制在某个集合 \$s\$ 内的情形。

这些定义在数学上对应于：**函数 \$f\$ 在点 \$x\$ 处（或在 \$x\$ 处相对于 \$s\$）的梯度为向量 \$f'\$**，当且仅当
$ f(x') - f(x) - \langle f',\, x' - x\rangle = o(\|x'-x\|) \quad (x' \to x,\, x' \in s).$

这里 \$o(|x'-x|)\$ 表示比 \$|x'-x|\$ 高阶的无穷小，即 \$\lim\_{x'\to x} \frac{|f(x') - f(x) - \langle f', x'-x\rangle|}{|x'-x|} = 0\$。直观来说，\$f'\$ 通过内积与增量 \$x'-x\$ 相乘，可以一阶近似 \$f\$ 的增量，这正是梯度的定义。

## 梯度向量与 Fréchet 导数的关系

接下来，代码定义了**梯度向量**（gradient）的提取函数，以及它和 Lean4 中 Fréchet 导数 (`fderiv`) 之间的关系：

```lean
/-- Gradient of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasGradientWithinAt f f' s x`), then
`f x' = f x + ⟨f', x' - x⟫ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

/-- Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
Denoted as `∇` within the Gradient namespace.

If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟫ + o (x' - x)` where `x'` converges to `x`. -/
def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped Gradient
```

\*\*解释：\*\*这段代码定义了 **梯度函数**，用于从函数的 Fréchet 导数提取梯度向量：

* \*\*`gradientWithin f s x`：\*\*返回函数 `f` 在点 `x` 处（相对于集合 `s`）的梯度向量。如果梯度存在就返回该向量，否则返回零向量。实现上，它通过 `(toDual 𝕜 F).symm` 将 Fréchet 导数 `fderivWithin 𝕜 f s x`（这是一个连续线性泛函 \$F \to 𝕜\$）转换回 Hilbert 空间中的向量。这里 `(toDual 𝕜 F)` 是把向量转换为对偶（线性泛函），因此它的逆 `(toDual 𝕜 F).symm` 把对偶元素转换回向量。这正是利用 Hilbert 空间的性质：在 Hilbert 空间中，每个线性泛函都对应唯一的梯度向量。

* \*\*`gradient f x`：\*\*返回函数 `f` 在点 `x` 处的梯度向量。如果梯度存在就返回它，否则返回零。同样，通过 Fréchet 导数 `fderiv 𝕜 f x` 转换得到向量。注意 `fderivWithin` 和 `fderiv` 的区别：`fderivWithin 𝕜 f s x` 是 \$f\$ 在 \$x\$ 处相对于 \$s\$ 的导数，而 `fderiv 𝕜 f x` 是全局导数。

Lean4 随后用 `notation "∇" => gradient` 定义了符号记号 **“∇”** 表示梯度函数，这样可以方便地写作 `∇ f x` 表示梯度。同一行 `local notation "⟪ x, y ⟫" => inner 𝕜 x y` 则引入了内积的符号记号，方便在 Lean 中书写 \$\langle x, y\rangle\$ 表示内积。

综上，这部分代码提供了在 Lean 中**计算梯度向量**的方法：Fréchet 导数 `fderiv` 给出的是一个线性映射（属于对偶空间），利用 Hilbert 空间内积，我们用 `(toDual 𝕜 F).symm` 将其转换回原空间的一个向量，这个向量就是我们通常意义下的梯度。

\*\*小结：\*\*到目前为止，我们有以下概念：

* `HasGradientAt f f' x` 表示 \$f'(x)\$ 是 \$f\$ 在 \$x\$ 处的梯度（如果存在）。
* `∇ f x` 给出 \$f\$ 在 \$x\$ 的梯度向量（若存在，不存在则返回 \$0\$），它实际是 `fderiv f x` 对偶映射对应的向量。

## 梯度与 Fréchet 导数等价性的定理

代码接下来通过一系列引理阐述 **HasGradient** 和 **HasFDeriv** （Fréchet 导数存在）的等价关系，以及一些基本性质。这些定理表明，用梯度向量描述的导数存在性，与 Lean4 内置的 Fréchet 导数定义是一致的：

```lean
variable {s : Set F} {L : Filter F}

theorem hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x :=
  Iff.rfl

theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : F →L[𝕜] 𝕜} {s : Set F} :
    HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, (toDual 𝕜 F).apply_symm_apply frechet]

theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x :=
  Iff.rfl

theorem hasFDerivAt_iff_hasGradientAt {frechet : F →L[𝕜] 𝕜} :
    HasFDerivAt f frechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [hasGradientAt_iff_hasFDerivAt, (toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt
alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt
alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt
alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt
```

**解释：**这一系列 `theorem`（定理）提供了**梯度存在**和**Fréchet 导数存在**之间的等价关系：

* `hasGradientWithinAt_iff_hasFDerivWithinAt` 给出了 `HasGradientWithinAt f f' s x` 和 `HasFDerivWithinAt f (toDual 𝕜 F f') s x` 是等价的，`Iff.rfl` 表示这是直接由定义展开即可证明的（同义反复）。意思是：*函数在 \$x\$ 处（相对于 \$s\$）具有梯度 \$f'\$* 与 *函数在 \$x\$ 处（相对于 \$s\$）具有 Fréchet 导数，其对应的连续线性映射为 `toDual 𝕜 F f'`* 是一回事。由于 `toDual 𝕜 F f'` 正是将梯度向量 \$f'\$ 转换成线性函数（通过内积计算微分），两种说法本质相同。

* `hasFDerivWithinAt_iff_hasGradientWithinAt` 是上一个定理的逆向表述：如果存在某个连续线性映射 `frechet` 作为 \$f\$ 在 \$x\$ 的 Fréchet 导数，那么 `frechet` 必定等于某个向量通过 `toDual` 映射得到的结果，而且这个向量就是梯度。用公式说，即若 \$\exists frechet: HasFDerivWithinAt f frechet s x\$，则必有 \$frechet = \mathrm{d}f(x)\$，并且 \$\mathrm{d}f(x)\$ 对应的梯度向量 \$(toDual 𝕜 F)^{-1}(frechet)\$ 满足 `HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x`。证明里用了 `(toDual 𝕜 F).apply_symm_apply frechet`，表明从对偶映射转换回向量然后再转回对偶，会得到原来的映射。

* `hasGradientAt_iff_hasFDerivAt` 以及 `hasFDerivAt_iff_hasGradientAt` 是全空间情况下梯度与导数的等价，同理：在没有子集限制时，\$f\$ 在 \$x\$ 有梯度 \$f'\$ 当且仅当有 Fréchet 导数 \$(toDual 𝕜 F f')\$。

这些定理通过 `↔` 表明两个命题逻辑上等价。Lean4 中使用了 `alias` 命令引入简化的推理规则，比如：

* `HasGradientWithinAt.hasFDerivWithinAt` 允许我们从 `HasGradientWithinAt` 推出对应的 `HasFDerivWithinAt`；
* `HasFDerivAt.hasGradientAt` 允许我们从 Fréchet 导数存在推出梯度存在，等等。

这些等价性确保我们在 Hilbert 空间内定义的梯度概念与标准分析中的 Fréchet 导数完全一致，不会产生歧义。

## 梯度的唯一性与基本性质

在确认了梯度存在性的定义后，代码给出了一系列定理，说明梯度的**唯一性**和其它基本性质，如不可微时梯度为零、存在梯度则可导以及反之等：

```lean
theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient, fderiv_zero_of_not_differentiableAt h, map_zero]

theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, gradient, (toDual 𝕜 F).apply_symm_apply (fderiv 𝕜 f x)]
  exact h.hasFDerivAt

theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, gradientWithin,
    (toDual 𝕜 F).apply_symm_apply (fderivWithin 𝕜 f s x)]
  exact h.hasFDerivWithinAt

theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.hasFDerivWithinAt.differentiableWithinAt

@[simp]
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt

theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h

theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient
```

\*\*解释：\*\*这些定理巩固了梯度概念的正确性和实用性：

* **不可微时梯度为零：**`gradient_eq_zero_of_not_differentiableAt` 表明，如果 \$f\$ 在 \$x\$ 处不可微（命题 `¬DifferentiableAt 𝕜 f x`），那么按照定义 `∇ f x` 会是零向量。这条定理通过使用 `fderiv_zero_of_not_differentiableAt`（不可微时 Fréchet 导数为零映射）和 `map_zero`（零映射对应零向量）得到结论。直观理解：若函数在某点没有导数，那么我们约定其梯度为零。

* **梯度唯一性：**`HasGradientAt.unique` 说明如果函数 \$f\$ 在 \$x\$ 处有梯度，并且我们找到了两个候选向量 `gradf` 和 `gradg` 都满足梯度定义，那么它们必定相等。证明中 `(toDual 𝕜 F).injective` 利用了 `toDual` 这个映射的单射性（不同的向量映射后是不同的线性函数）。也就是说，梯度（如果存在）是唯一的。

* **存在梯度当且仅当可微：**`DifferentiableAt.hasGradientAt` 和 `HasGradientAt.differentiableAt` 互相表明了**梯度存在**与**可微性**（Fréchet 导数存在）的等价：

  * 如果 \$f\$ 在 \$x\$ 处可微（`DifferentiableAt 𝕜 f x`），那么梯度存在且 `∇ f x` 就是那个梯度向量 (`HasGradientAt f (∇ f x) x`)。
  * 反过来如果 `HasGradientAt f f' x` 成立，则意味着 Fréchet 导数存在，所以 \$f\$ 在 \$x\$ 可微 (`DifferentiableAt 𝕜 f x`)。

  这再次验证了 Hilbert 空间中梯度概念与可微性的吻合。

* \*\*相对于集合的可微与梯度：\*\*同样的对应关系也适用于局部可微：

  * `DifferentiableWithinAt.hasGradientWithinAt` 说明如果 \$f\$ 在 \$x\$ 相对于 \$s\$ 可微，那么存在梯度且 `gradientWithin f s x` 给出的正是该梯度。
  * `HasGradientWithinAt.differentiableWithinAt` 则是逆命题：有梯度意味着可微（相对于 \$s\$）。

* \*\*`hasGradientWithinAt_univ` 化简：\*\*这一条指出如果把 `s` 取为 `univ`（全空间），`HasGradientWithinAt f f' univ x` 当且仅当 `HasGradientAt f f' x`。由于 `𝓝[univ] x = 𝓝 x`，这只是一个一致性检查，Lean4 用 `@[simp]` 标记它为一个化简规则。

* **可微于某集合上的函数在包含该点的邻域内也有梯度：**`DifferentiableOn.hasGradientAt` 说，如果 \$f\$ 在集合 \$s\$ 上处处可微，且 \$s`在 $x$ 附近作为邻域（$s ∈ 𝓝 x$，也就是 $x$ 是 $s$ 的内点），那么 $f$ 在 $x$ 也有全局梯度`∇ f x\`。

* **提取已存在的梯度值：**`HasGradientAt.gradient` 是一个方便使用的引理：如果我们知道 `HasGradientAt f f' x`，那么实际上 `∇ f x = f'`。也就是梯度函数计算出来的值和假设存在性的向量相符。

* **梯度函数等于给定函数：**`gradient_eq` 这个定理表示，如果对于每个 \$x\$ 都存在梯度且某个函数 \$f'(x)\$ 总是那个梯度，那么 `∇ f = f'` 作为两个函数（从 \$F\$ 到 \$F\$）是相等的。这通常用来在整体上确定梯度函数的表达式。

归纳来说，这些性质保证：**梯度的定义与可微分函数理论保持一致**（存在唯一的梯度当且仅当函数可微），并且提供了一些方便在 Lean4 中操作梯度的工具。特别注意，在 Hilbert 空间下，因为 Riesz 表示定理，梯度才存在且唯一，并由对偶空间元素对应 —— Lean4 通过 `toDual` 和其逆精确地捕获了这种对应关系。

## 一维情形下的梯度与导数

在 Hilbert 空间中，\$F\$ 可以是任意维度，包括无限维。但当 \$F = 𝕜\$ 时（也就是 \$F\$ 本身就是 \$\mathbb{R}\$ 或 \$\mathbb{C}\$，**实数轴或复数平面**），梯度概念应当退化为我们熟知的一维**导数**。代码中特别处理了一维情况，给出了梯度与一元导数的等价关系和简化形式：

```lean
section OneDimension

variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (starRingEnd 𝕜 g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (starRingEnd 𝕜 g') = (toDual 𝕜 𝕜) g' := by
    ext; simp
  rwa [HasDerivAtFilter, this]

theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' u L') :
    HasGradientAtFilter g (starRingEnd 𝕜 g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (starRingEnd 𝕜 g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) :
    HasDerivAt g (starRingEnd 𝕜 g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) :
    HasGradientAt g (starRingEnd 𝕜 g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
  simpa

theorem gradient_eq_deriv : ∇ g u = starRingEnd 𝕜 (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]
```

```lean
section OneDimensionReal

variable {g : ℝ → ℝ} {g' u : ℝ} {L' : Filter ℝ}

theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' u L' := h.hasDerivAtFilter

theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' u L') :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter

theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt

theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt

theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv
```

\*\*解释：\*\*这一部分讨论 \$F = 𝕜\$ 的特殊情况。在这种情形下，函数 \$g: 𝕜 \to 𝕜\$（实函数或复函数）的梯度应该等同于它的一维导数，因此提供了一些引理来相互转换：

* \*\*复数情形（一般 \$𝕜\$）：\*\*上面的 `section OneDimension` 针对 \$𝕜\$ 可以是 \$\mathbb{R}\$ 或 \$\mathbb{C}\$ 的通用情况，其中需要考虑复数的共轭问题：

  * `HasGradientAtFilter.hasDerivAtFilter` 和 `HasDerivAtFilter.hasGradientAtFilter` 证明了：\$g\$ 在 \$u\$ 处沿过滤器 \$L'\$ 有梯度 \$g'\$ 当且仅当 有导数 \$g'\$ （这里的 \$g'\$ 作为导数要考虑复共轭，由 `starRingEnd 𝕜` 给出）。

    * `starRingEnd 𝕜 g'` 通常表示将 \$g'\$ 应用“星”自同态（对于复数就是共轭，对于实数就是恒等），因为在 Hilbert 空间定义梯度时对复数场需要取共轭来匹配标准的内积导数关系。如果 \$𝕜 = \mathbb{C}\$，梯度与导数的对应需要一个复共轭。
    * 证明中，`ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (starRingEnd 𝕜 g') = (toDual 𝕜 𝕜) g'` 的含义是：将标量乘法映射（恒等映射 1 乘以标量）作用在 \$starRingEnd 𝕜 g'\$ 上，得到的正是 \$toDual 𝕜 𝕜 g'\$。这其实在说，一维情况下 Fréchet 导数（一个从 \$\mathbb{R}\$ 或 \$\mathbb{C}\$ 到 \$\mathbb{R}\$ 或 \$\mathbb{C}\$ 的线性映射）等价于乘以某个标量，而这个标量就是导数值（对于复数是共轭后的值）。
  * `HasGradientAt.hasDerivAt` 和 `HasDerivAt.hasGradientAt` 将上述过滤器情况特例化为通常的点处导数：在 \$u\$ 处有梯度 \$g'\$ 等价于在 \$u\$ 处有导数 \$g'\$（注意依然涉及 `starRingEnd` 共轭）。
  * `gradient_eq_deriv` 直接给出了梯度值与导数值的关系：\$\nabla g(u) = \text{starRingEnd}\_𝕜(,g'(u),)\$，这里 \$g'(u) = deriv\ g\ u\$ 是 Lean4 记号表示的导数值。如果 \$g\$ 在 \$u\$ 不可微，则两边都是 \$0\$。对于实数情况 \$\text{starRingEnd}\_ℝ\$ 是恒等，所以 \$\nabla g(u) = g'(u)\$；对于复数情况 \$\text{starRingEnd}\_ℂ(z) = \overline{z}\$ 共轭，所以 \$\nabla g(u) = \overline{g'(u)}\$。之所以对复数取共轭，是因为 Hilbert 空间（复内积空间）中的导数被认为是共轭线性对应的梯度向量。

* \*\*纯实情形：\*\*接下来的 `section OneDimensionReal` 假定 \$𝕜 = \mathbb{R}\$，也就是 \$g: \mathbb{R} \to \mathbb{R}\$。在这种情况下，共轭运算无意义或说就是恒等，因此所有 `starRingEnd ℝ` 都可以去掉：

  * `HasGradientAtFilter.hasDerivAtFilter'` 等价于 `HasGradientAtFilter.hasDerivAtFilter` 只是省去了共轭，因为对于实数 \$g'\$ 和 \$\overline{g'}\$ 相同。
  * 这一部分提供的四条定理对应于前面的带撇版本，没有复杂操作：

    * 梯度存在蕴含导数存在，导数存在也蕴含梯度存在（在滤芯情形或点情形下，都成立）。
    * `gradient_eq_deriv'` 声明 \$\nabla g(u) = g'(u)\$，这是实数情况下梯度和导数直接相等的最终结论。

\*\*小结：\*\*对于一元实/复函数，Lean4 梯度定义与普通导数一致。这段代码确保在一维情形不会出现概念偏差：梯度就是导数（复数情况下严格说是导数的复共轭，但在实数下就完全一致）。因此，在 Hilbert 空间理论中，我们的梯度在退化为一维时，符合高中/大学基础微积分中导数的定义。

## 梯度定义的渐近等价条件（小 \$o\$ 记号和极限形式）

接下来代码给出**梯度定义的等价刻画**，使用了“小 \$o\$”（little-o）符号和极限形式，将 `HasGradient...` 的定义展开成极限关系。这有助于直观理解梯度的定义：

```lean
open Filter

section GradientProperties

theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x :=
  hasFDerivAtFilter_iff_isLittleO ..

theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h

theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties
```

\*\*解释：\*\*这一组定理将梯度存在的定义和极限形式联系起来，使我们更直接地从分析角度理解 `HasGradientAt` 等价于某个极限等于0或“小o”条件成立：

* **小 \$o\$ 表述：**
  `HasGradientAtFilter f f' x L ↔ (x' ↦ f(x') - f(x) - ⟪f', x'-x⟫) = o[L] (x' ↦ x'-x)`.
  翻译成数学语言：\$f\$ 在 \$x\$ 处沿滤镜 \$L\$ 有梯度 \$f'\$ 当且仅当

  $$
  f(x') - f(x) - \langle f', x'-x\rangle = o(\|x'-x\|) \quad \text{（当 $x'$ 按 $L$ 趋于 $x$）},
  $$

  这正是梯度定义的渐进小 \$o\$ 条件。【注：这里 \$(g = o\[L] h)\$ 表示 \$g(x')/|h(x')| \to 0\$ 当 \$x'\$沿 \$L\$趋近相应点。】

  `hasGradientWithinAt_iff_isLittleO` 和 `hasGradientAt_iff_isLittleO` 分别针对 `𝓝[s] x` 和 `𝓝 x` 两种情况，但本质条件一样，只是限定 \$x' \to x\$ 时是否需在 \$s\$ 内。

* **极限趋于0的形式：**
  `HasGradientWithinAt f f' s x ↔ Tendsto (‖x'-x‖⁻¹ * ‖f(x') - f(x) - ⟪f', x'-x⟫‖) (𝓝[s] x) (𝓝 0)`.
  这展开来说，如果我们看比值 \$\frac{|f(x') - f(x) - \langle f', x'-x\rangle|}{|x'-x|}\$，当 \$x' \to x\$ 且 \$x' \in s\$ 时，该比值趋于0。当没有子集限制时（即 \$s = \$ 全空间），就得到 `hasGradientAt_iff_tendsto`：梯度存在当且仅当
  $\lim_{x' \to x} \frac{\|f(x') - f(x) - \langle f', x'-x\rangle\|}{\|x'-x\|} = 0.$
  这正是 Fréchet 可微性的定义，只不过右侧强调梯度 \$f'\$ 以向量内积形式出现。

* **大 \$O\$ 表述：**
  `HasGradientAtFilter.isBigO_sub` 表明：如果 \$f\$ 在滤镜 \$L\$ 下有梯度，则 \$f(x') - f(x) = O(|x'-x|)\$（当 \$x' \to x\$）。**大 \$O\$** (\$O\$) 粗略来说表示不增长得比 \$|x'-x|\$ 更快。这个结论其实显然，因为如果 \$f(x') - f(x) = \langle f', x'-x\rangle + o(|x'-x|)\$，那显然是 \$O(|x'-x|)\$。Lean4 通过已知的 `HasFDerivAtFilter.isBigO_sub` 性质得到它。

* **集合改变的等价：**
  这几条 `hasGradientWithinAt_congr_set'` 和 `hasGradientWithinAt_congr_set` 则讨论如果我们在 \$x\$ 附近改变集合 \$s\$ 一个“微小”的部分，不影响梯度存在性的判断。
  具体说，`h : s =ᶠ[𝓝[{y}ᶜ] x] t` 表示在 \$x\$ 附近除了可能点 \$y\$ 外，\$s\$ 和 \$t\$ 是一样的（这里 \$\mathcal{N}\[{y}^c] x\$ 表示“在 \$x\$ 附近且不包含 \$y\$”的邻域过滤器）。在这种情况下，\$f\$ 在 \$x\$ 对 \$s\$ 有梯度当且仅当 对 \$t\$ 也有梯度。简化版 `hasGradientWithinAt_congr_set` 则是若在 \$x\$ 的邻域内 \$s\$ 和 \$t\$ 本身就最终一致 (`s =ᶠ[𝓝 x] t`)，那么两者梯度存在是等价的。
  这意味着判断梯度存在与否是一个局部性质，改变远离 \$x\$ 的部分（或不影响 \$x\$ 附近点收敛的集合差异）不会改变结论。

* **零邻域形式：**
  `hasGradientAt_iff_isLittleO_nhds_zero` 以另一种方式表述梯度：考虑 \$h = x'-x\$ 作为增量向量，那么 \$h \to 0\$ 时
  $f(x+h) - f(x) - \langle f', h\rangle = o(\|h\|).$
  这和上述定义一致，但从 \$h\$ 的角度来看，就是在零向量邻域的过滤器 \$\mathcal{N}(0)\$ 下满足小 \$o\$。

总之，这些定理将梯度存在转化为我们熟悉的极限形式、\$o\$-小量和\$O\$-有界量条件，使概念更直观：**梯度就是使函数增量与线性近似之差相对于增量范数趋于0的那个向量**。

## 函数一致变化对梯度的影响（一致性性质）

有时，我们关心如果两个函数在某点附近相等（或在某集合上相等），那么它们的梯度关系如何。代码接下来提供了一组“congr”（一致/一致性）定理，说明在函数局部替换的情况下梯度结论不变：

```lean
section congr

variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {t : Set F}

theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  h₀.hasFDerivAtFilter_iff hx (by simp [h₁])

theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)

theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr
```

**解释：**这部分定理讨论了**当两个函数局部相等时梯度的传递性**：

* 首先要理解 Lean4 中 `f₀ =ᶠ[L] f₁` 的记号，`EventuallyEq` (缩写 `.=`) 表示\*\*“最终相等”\*\*，也就是存在一个过滤器 \$L\$ 的某个集合，在那上面 \$f₀\$ 与 \$f₁\$ 的值相等。常见的如 `f₁ =ᶠ[𝓝 x] f` 表示在 \$x\$ 的某个邻域上 \$f₁\$ 和 \$f\$ 重合（可能不在整个邻域，但在邻域内的一个子集上都相等，这已经足够，因为过滤器看“最终行为”）。

* `Filter.EventuallyEq.hasGradientAtFilter_iff`：如果 \$f₀\$ 和 \$f₁\$ 在滤镜 \$L\$ 下**最终相等**（并且在点 \$x\$ 处函数值也一样），且假定 \$f₀'\$ 和 \$f₁'\$ 是相等的向量，那么 \$f₀\$ 在 \$x\$ 处沿 \$L\$ 有梯度 \$f₀'\$ 当且仅当 \$f₁\$ 在 \$x\$ 处沿 \$L\$ 也有梯度 \$f₁'\$。简言之，在点附近两个函数没有区别，那么梯度存在性也完全一致，并且梯度值相同。

* `HasGradientAtFilter.congr_of_eventuallyEq`：如果已知 \$f\$ 在 \$x\$ 沿 \$L\$ 有梯度 \$f'\$ (`h` 前提)，而 \$f₁\$ 与 \$f\$ 在滤镜 \$L\$ 下局部一致（尤其在 \$x\$ 处值也一样），那么可以推得 \$f₁\$ 在 \$x\$ 沿 \$L\$ 也有梯度 \$f'\$。这实际是前一个定理的推论，去掉了双向条件，只留下从 \$f\$ 推到 \$f₁\$ 的一向。

* `HasGradientWithinAt.congr_mono`：这个定理处理子集情形。如果 \$f\$ 在 \$x\$ 相对于 \$s\$ 有梯度 \$f'\$，并且 \$f₁\$ 在较小的子集 \$t ⊆ s\$ 上与 \$f\$ 的函数值相同（特别地在 \$x\$ 点它们相同），那么 \$f₁\$ 在 \$x\$ 相对于 \$t\$ 也有梯度 \$f'\$。因为 \$t\$ 内部 \$f₁\$ 和 \$f\$ 没区别，所以 \$f₁\$ 限制在 \$t\$ 上的行为和 \$f\$ 在 \$t\$ 上一样，自然继承梯度性质。

* `HasGradientWithinAt.congr` 是 `congr_mono` 的一种特例：当 \$f₁\$ 在整个集合 \$s\$ 上都与 \$f\$ 相同（那就是 \$f₁\$ 实际等于 \$f\$ 在 \$s\$ 上），那么显然 \$f\$ 有梯度就推出 \$f₁\$ 有梯度，而且是相同梯度。

* `HasGradientWithinAt.congr_of_mem` 也是类似推论，要求 \$x ∈ s\$ 且在 \$s\$ 上 \$f₁=f\$。和 `congr` 几乎一样，只是强调 \$x\$ 要在 \$s\$ 中（其实如果 \$x\$ 不在 \$s\$，`HasGradientWithinAt f ... s x` 本身就没什么意义，因为我们通常讨论 \$x\$ 是 \$s\$ 内点的情况）。

* `HasGradientWithinAt.congr_of_eventuallyEq` 与 `HasGradientWithinAt.congr_of_eventuallyEq_of_mem`：这两条将“最终在邻域相等”的概念引入 \$s\$ 内。
  如果 \$f₁ =ᶠ\[𝓝\[s] x] f\$ （即存在 \$x\$ 的一个邻域，在该邻域与 \$s\$ 的交集上 \$f₁\$ 与 \$f\$ 重合），并且在 \$x\$ 点它们值也相同，那么 \$f\$ 在 \$s\$ 上有梯度蕴含 \$f₁\$ 在 \$s\$ 上有梯度（梯度向量相同）。
  带 `_of_mem` 的版本再次只是强调 \$x∈s\$ 的情形，保证讨论梯度时 \$x\$ 在域内。

* `HasGradientAt.congr_of_eventuallyEq`：是全空间情形下的版本。如果 \$f₁\$ 在 \$x\$ 的某邻域与 \$f\$ 重合，那么 \$f\$ 在 \$x\$ 有梯度 \$f'\$ 推出 \$f₁\$ 在 \$x\$ 也有梯度 \$f'\$。

* **梯度值的一致性：**
  `Filter.EventuallyEq.gradient_eq` 声明如果 \$f₁\$ 在 \$x\$ 附近等于 \$f`，那么 $\nabla f₁(x) = \nabla f(x)$。证明中 `unfold gradient; rwa \[Filter.EventuallyEq.fderiv\_eq]`说明它利用了 $f₁$ 和 $f$ 有相同的 Fréchet 导数（因此 $fderiv f₁ x = fderiv f x$），从而梯度向量相同。  `Filter.EventuallyEq.gradient\` 则提升为一个在邻域过滤器下的等式：\$\nabla f₁ =ᶠ\[𝓝 x] \nabla f\$，即在 \$x\$ 附近两者梯度作为函数也处处相等。

这些结果告诉我们：**梯度是局部属性**，只取决于函数在局部的表现。如果两个函数在某点附近没有区别，它们的可微性和梯度信息也是没有区别的。这对在证明题时经常有用——可以在不改变局部特性的情况下修改函数而不影响梯度的结论。

## 常数函数的梯度

常数函数是一个极端简单的例子，它处处可微且导数为零，那么按照梯度定义，也应得到梯度为零向量。代码对此也给出了定理：

```lean
/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter, map_zero]; apply hasFDerivAtFilter_const c x L

theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _

theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x :=
  hasGradientAtFilter_const _ _ _

theorem gradient_fun_const : ∇ (fun _ => c) x = 0 := by simp [gradient]

theorem gradient_const : ∇ (const F c) x = 0 := gradient_fun_const x c

@[simp]
theorem gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0 :=
  funext fun x => gradient_const x c

@[simp]
theorem gradient_const' : ∇ (const F c) = 0 := gradient_fun_const' c

end Const
```

\*\*解释：\*\*这里 `fun _ => c` 表示值恒等于 `c` 的常数函数。结论一目了然：

* `hasGradientAtFilter_const` 断言无论在哪个过滤器 \$L\$ 下，常值函数都有梯度 \$0\$。证明中 `map_zero` 表示把 \$0\$ 向量通过 `toDual` 映射仍是零函数，然后 `hasFDerivAtFilter_const c x L` 表明常数函数的 Fréchet 导数存在且为零映射。于是梯度满足定义。

* `hasGradientWithinAt_const` 和 `hasGradientAt_const` 是特例：无论在任何集合上或全空间，常数函数在任何点的梯度都是0。这只是用上条结论的直接推论。

* `gradient_fun_const` 明确给出 \$\nabla (\text{常数函数}) (x) = 0`。证明通过 `simp \[gradient]\` 即可，Lean 能简化出梯度的定义然后用导数为零的事实。

* `gradient_const` 把常数函数换一种写法 `const F c`（Lean 中 `const F c` 表示定义域类型为 `F` 的常值函数）也是0。

* 带 `'` 的定理 `gradient_fun_const'` 和 `gradient_const'` 则声明**整个梯度函数**本身就是零函数，而不仅仅某点为零。用 `funext`（函数外延性原理）证明，即对任意 `x` 都成立，从而两个函数相等。这些被标记为 `@[simp]` 以方便 Lean 自动化处理常数梯度情形。

直观理解：**常数函数的梯度处处为零向量**，这一点完全符合我们对导数的认识，也验证了前面梯度定义的合理性。

## 梯度存在与连续性

最后，代码讨论了梯度存在蕴含函数连续的性质。众所周知，若函数在某点可微，则一定在该点连续。下面将这条性质套用在梯度定义上：

```lean
section Continuous

/-! ### Continuity of a function admitting a gradient -/

nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL

theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h

theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h

protected theorem HasGradientAt.continuousOn {f' : F → F} (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

end Continuous
```

\*\*解释：\*\*这一部分表明，如果函数在某点有梯度，那么在该点函数必定连续；如果在某集合上处处有梯度，那么函数在该集合上连续：

* `HasGradientAtFilter.tendsto_nhds`：如果 \$L\$ 是一个滤镜且 \$L \le \mathcal{N}(x)\$（意思是 \$L\$ 至少包含趋于 \$x\$ 的信息，例如 \$L\$ 可能就是 \$\mathcal{N}(x)\$ 本身或者更粗略），并且 \$f\$ 在 \$x\$ 处沿 \$L\$ 有梯度，那么 \$f(x')\$ 当 \$x'\$ 沿 \$L\$ 趋于 \$x\$ 时，会收敛到 \$f(x)\$。这正是说 \$f(x') \to f(x)\$，也即 \$f\$ 在 \$x\$ 处（沿滤镜 \$L\$）连续。这里 `h.tendsto_nhds hL` 是利用 Fréchet 导数存在蕴含连续的性质，因为有导数必连续。

* `HasGradientWithinAt.continuousWithinAt`：如果 \$f\$ 在 \$x\$ 相对于 \$s\$ 有梯度，那么 \$f\$ 在 \$x\$ 相对于 \$s\$ 连续。证明里用了 `inf_le_left`，这是因为 \$\mathcal{N}\[s] x = \mathcal{N}(x) \cap\$ something，所以至少比邻域过滤器更细，从而应用上条结果。

* `HasGradientAt.continuousAt`：这是全空间情形的特例：在 \$x\$ 有梯度则在 \$x\$ 连续。这一点符合直觉：可微必连续。

* `HasGradientAt.continuousOn`：若对于每个 \$x ∈ s\$，\$f\$ 在 \$x\$ 有梯度（相应梯度向量可能因 \$x\$ 而异，这里假设存在函数 \$f'(x)\$ 给出每点的梯度），那么 \$f\$ 在整个 \$s\$ 上是连续的。证明是针对任意 \$x ∈ s\$，从假设 \$(h x hx).continuousAt` 得到 $f` 在 \$x\$ 连续，然后因为这是对 \$s\$ 内每个点都成立，所以 \$f\$ 在 \$s\$ 上连续。

这些定理再一次印证：**梯度存在（可微）蕴含连续**。虽然结论对熟悉微积分的人来说是显然的，但是在形式化证明中需要此桥梁。Lean4 在这里将这一事实通过 `HasGradient...` 系列定义联系了起来。

---

以上，我们逐行解释并对应了 Lean4 代码中 Hilbert 空间函数梯度的定义及其主要性质。总结而言：

* 梯度的定义捕捉了函数在 Hilbert 空间中 Fréchet 可微时，对应线性泛函（导数）的那个向量表示。
* 梯度存在性与 Fréchet 导数存在性等价，可看成是同一个事实的不同表述。
* 梯度在定义域的一致改变下保持稳定，常数函数的梯度为零，这些都符合直觉。
* 在一维情形下，梯度退化为普通导数，符合常识。
* 函数有梯度必连续，以及相关的极限定义，都保证了理论的完备性。

通过 Lean4 形式化，我们确保这些结论都被严格证明，因此整个理论体系在形式上是自洽且可靠的。
