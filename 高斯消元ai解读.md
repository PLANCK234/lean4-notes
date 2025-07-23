## 高斯消元代码阅读

好的，我将为你整理这段代码中涉及的所有内容，生成一个完整的 Markdown 源代码文档，包括：

* 所有用到的 Lean tactic 的名称、用法、定义和示例；
* 所涉及的 Lean 数学/结构概念，如 `Gaussian`、`Matrix` 操作、`Perm`、`GL` 等的定义和解释；
* 所有涉及的公式、函数、自定义定义（def）及其功能概述。

我整理好后会将它返回给你，你可以作为学习参考或文档归档使用。


### Basic 部分

#### `swap_rows`（交换行）

定义：`swap_rows M i j` 返回矩阵 `M` 的一个新矩阵，其中第 `i` 行和第 `j` 行对换。实现上使用了 `M.submatrix (swap i j) id`，其中 `swap i j` 是一个将行索引 `i` 和 `j` 交换的置换。
用法：交换矩阵的两行。例如，`#check swap_cols`（注：这里 `swap_cols` 利用 `swap_rows` 实现列交换，下面详述）用于检查类型，`#eval swap_cols !![0,1; 2,1] 0 1` 可以用于测试交换第一列和第二列的效果。

#### `swap_cols`（交换列）

定义：`swap_cols M i j` 返回矩阵 `M` 的一个新矩阵，其中第 `i` 列和第 `j` 列对换。实现思想是通过转置矩阵、交换行，再转置回来：`swap_cols M i j = (swap_rows M.transpose i j).transpose`。
用法：交换矩阵的两列。调用例如 `swap_cols M i j` 将实现列 `i` 和列 `j` 的互换。

#### `scale_row`（行数乘标量）

定义：`scale_row M i c` 将矩阵 `M` 的第 `i` 行按标量 `c` 进行缩放（数乘）。实现使用 `updateRow M i <| c • (M i)`，即将第 `i` 行更新为原第 `i` 行乘以系数 `c`。这个定义要求类型 `α` 上定义了标量乘法 `SMul 𝕜 α`。
用法：将某一行所有元素同时乘以系数。例如，`#eval scale_row !![0,0; 1,1] 1 2` 会将矩阵的第1行（索引0）乘以2。

#### `add_row_multiple`（行倍加）

定义：`add_row_multiple M i j c` 返回矩阵，其第 `i` 行更新为“原第 `i` 行 + 系数 `c` × 原第 `j` 行”。实现用法：`updateRow M i <| (M i) + c • (M j)`。要求元素类型 `α` 支持加法 `Add α`。
用法：对第 `i` 行做初等行变换：`Ri := Ri + c * Rj`。例如，`#eval add_row_multiple !![0,0; 1,1] 0 1 2` 将第0行替换为第0行 + 2×第1行。

#### `gaussian_update`（高斯消元更新函数）

定义：`gaussian_update M i k a b` 是一个辅助函数，输出一个函数（行映射）用于更新矩阵行。它根据主元所在的行 `i` 及列消元系数 `a`、`b` 定义如下：如果当前行索引 `k ≤ i`，则返回原矩阵第 `k` 行不变；如果 `k > i`（在主元行以下），则返回 `a * M k - b * M i`。这个公式体现了用第 `i` 行的倍数去消去第 `k` 行对应列元素的操作：通常 `a` 会取1，`b` 为消元系数，使得第 `k` 行第 `j` 列元素消为0。该函数需要 `α` 支持加法、乘法、减法和取负（对应环的运算）。

#### `gaussian_update_row`（按行的高斯更新）

定义：`gaussian_update_row M i j` 利用上述 `gaussian_update` 函数，对矩阵 `M` 执行以第 `i` 行、第 `j` 列元素为主元的消元操作，返回更新后的矩阵。实现：`fun k => gaussian_update M i k (M i j) (M k j)`，即对于每一行 `k`，如果在主元行下面，则用 `a = M i j` 和 `b = M k j` 来计算新的第 `k` 行。这样会将第 `k` 行的第 `j` 列元素消为0。

*(注：代码中还草稿式地提到了 `gaussian_update_col`（按列的高斯更新），但该定义被注释掉未实际使用。)*

### Gaussian 结构体

#### `Gaussian` 结构

定义：`Gaussian n m α` 是一个结构体，用于封装高斯消元过程中的矩阵及其变换。它包含：

* `M`：原始矩阵（类型 `Matrix (Fin n) (Fin m) α`）。
* `R`：经过消元后的矩阵（结果矩阵）。
* `P`：一个可逆的行变换矩阵（`n×n` 矩阵），表示对原矩阵进行的行操作。
* `Q`：一个可逆的列变换矩阵（`m×m` 矩阵），表示对原矩阵进行的列操作。
  并且满足关系式 `P * M * Q = R`，即 `R` 可以由 `M` 左乘 `P`、右乘 `Q` 得到。这个结构体把高斯消元中涉及的 \$P\$、\$Q\$、\$R\$、原矩阵 \$M\$ 打包在一起，方便表示消元过程的结果。
  *(注：注释中提到 `P M Q = [I_r, 0; 0, 0]`，表示最终希望通过选取适当的 \$P\$、\$Q\$，将矩阵化为一种标准形，其中左上角是秩为 \$r\$ 的单位块，其余部分为0。)*

#### `Gaussian.transpose`（高斯结构转置）

定义：`M.transpose` 将一个 `Gaussian n m α` 结构转置，返回对应的 `Gaussian m n α`。其具体操作是：

* 将原来的 `P` 矩阵替换为 `M.Q.transpose`（将列变换矩阵转置作为新的行变换矩阵）；
* 将原来的 `Q` 矩阵替换为 `M.P.transpose`；
* 将原来的 `R` 和 `M` 矩阵都转置；
  这样得到的新结构仍满足关系式：`(M.transpose).P * (M.transpose).M * (M.transpose).Q = (M.transpose).R`。也就是说，整个高斯消元结构转置后依然保持 \$P M Q = R\$ 的关系。这个函数便于将行操作的结果转化为等效的列操作结果。

### Gauss 部分（高斯消元过程）

#### `gaussian_elimination_step_row`（单步高斯消元——行消元）

定义：`gaussian_elimination_step_row M i j hM` 对 `Gaussian M` 执行一次以行为主的消元步骤。其中 `i` 是当前消元的主元行，`j` 是主元列，条件 `hM : M.R i j ≠ 0` 表示当前位置 `(i,j)` 的主元不为0。该函数构造并返回一个新的 `Gaussian`：

* 新的 `P` 通过 `fun k => gaussian_update M.P i k (M.R i j) (M.R k j)` 计算，表示对当前 `P` 进行与消元相应的行变换（对应左乘操作，使得保持等式成立）。
* 新的 `R` 使用 `gaussian_update_row M.R i j` 来消去 `R` 中主元下方同列的元素（把第 `j` 列中第 `i` 行下面的元素消为0）。
* `Q` 保持不变（因为此步是行消元，对列没有操作）。
* `M` 保持不变（原矩阵始终不变，仅记录）。
  经过此函数，矩阵 `R` 在第 `j` 列主元下方的元素被消为0，相应的 `P` 累积了这一行操作。

#### `gaussian_elimination_step_col`（单步高斯消元——列消元）

*（注：此函数在代码中被注释掉，尚未完成实现。它意在实现按列的消元步骤，与 `gaussian_elimination_step_row` 类似但作用在列上。）*

#### `find_pivot_col`（找主元行）

定义：`find_pivot_col M_row i` 用于在第 `i` 行及以下，寻找当前列中绝对值最大的元素的行索引（主元行）。它返回一个 `Fin n` 类型的索引。实现时利用了 `argmax` 函数对列表进行索引比较：`(argmax (abs ∘ M_row) ((finRange n).rtake (n - i))).getD 0`。意思是，从所有行索引构成的列表中截取从 `i` 开始到末尾的部分，对每个行 `k` 计算 `|M_row k|`，找出使该值最大的行索引。如果列表为空则默认返回0（`getD 0`)。
用法：通常传入参数 `M_row` 是一个函数，给定行返回矩阵中对应列的元素值，`i` 是当前处理的行索引。`find_pivot_col` 帮助实现部分主元选取，用来决定是否需要交换行以找到非零最大主元。
*(注：代码中使用了 `LinearOrder α` 和一个假定的 `abs` 函数来比较大小，这意味着元素类型 `α` 可以比较大小，如实数或整数等。)*

#### `gaussian_elimination_pivot_row`（主元选取——行方向）

定义：`gaussian_elimination_pivot_row M i j` 在进行行消元时，确保第 `i` 行第 `j` 列处有适合作为主元的非零元素。如果当前 `M.R i j` 过小或为零，则调用 `find_pivot_col (fun k => M.R k j) i` 找到从第 `i` 行开始在第 `j` 列“最大”的元素所在行 `z`。如果找到的主元行 `z` 不等于 `i` 本身，则交换行：

* 更新 `P := swap_rows M.P z i` 交换记录矩阵的这两行，
* 更新 `R := swap_rows M.R z i` 实际在消元矩阵中交换这两行。
  如果 `z = i`，则无需交换。`Q` 和 `M` 保持不变。
  这样经过 pivot 操作后，第 `i` 行拥有了该列的最大主元（或至少是一个非零主元），为后续消元做好准备。

#### `gaussian_elimination_row_aux`（高斯消元递归过程——行）

定义：`gaussian_elimination_row_aux M row hr col hc` 是行主元高斯消元的递归过程函数：

* 输入：`M` 是当前的 `Gaussian` 状态，`row` 和 `col` 是当前处理的行索引和列索引（普通自然数类型，但有界于 `n` 和 `m`），`hr : row < n` 和 `hc : col < m` 是索引界内的证明。
* 首先调用 `pivotA = gaussian_elimination_pivot_row M rown colm`（将第 `row` 行主元调整到位，其中 `rown`和`colm`是对应的Fin索引）。
* 接着分情况递归：如果还没到最后一行/列，即 `row < n-1` 且 `col < m-1`：

  * 若经选主元后 `pivotA.R rown colm = 0`（说明该列在此行没有非零值，可跳过），则递归调用自身但**列索引加1**（跳过这一列继续消元）：`gaussian_elimination_row_aux pivotA row hr (col+1) ...`。
  * 若 `pivotA.R rown colm ≠ 0`，则执行消元步骤：先计算 `nextA = gaussian_elimination_step_row pivotA rown colm h`（此时 `h` 证明确实非零），这会消去该列中该主元行以下所有元素；然后递归调用自身，行索引加1，列索引加1，继续处理下一行下一列主元：`gaussian_elimination_row_aux nextA (row+1) ... (col+1) ...`。
* 递归在超出界限或到矩阵边缘时终止，返回最终的 `Gaussian`。

为了让 Lean 接受这个递归（因使用了非常量递归步长），代码提供了显式的递归终止证明：

* 使用 `termination_by (n + m) - (row + col)` 指定递归度量：每次递归降低 `row + col` 的值相对于 `n+m`。
* 使用 `decreasing_by` 块内的证明：通过 `rw [tsub_lt_tsub_iff_left_of_le]` 和 `linarith` 等 tactics 证明每次递归调用前后的度量严格递减，从而保证函数会终止。

#### `gaussian_elimination_row`（按行高斯消元接口）

定义：`gaussian_elimination_row M` 是对外的高斯消元（行主元）入口。它检查矩阵是否有至少一行和一列（即 `0 < n ∧ 0 < m`）：

* 如果矩阵非空，则调用 `gaussian_elimination_row_aux M 0 h.1 0 h.2` 从第0行、第0列开始递归执行高斯消元，返回最终得到的 `Gaussian`。
* 如果矩阵维度为0，则直接返回原 `M`。
  结果：`gaussian_elimination_row M` 会得到一个 `Gaussian`，其中 `R` 矩阵为行梯形（Row Echelon Form）：即从上到下每行主元所在列位置严格递增，并且主元下方列元素皆为0。

#### `gaussian_elimination_col_aux`（高斯消元递归过程——列）

定义：`gaussian_elimination_col_aux M row hr col hc` 是按列主元的高斯消元递归函数。它的逻辑和行递归类似，但主元选择与递归推进方向相反：

* 在还未处理完矩阵时 (`row < n-1 ∧ col < m-1`)：

  * 若 `M.R rown colm = 0`，表示当前行在当前列没有主元，则**跳过当前行**（而不是跳过列）：递归调用自身，`row+1`（下一行），`col` 不变。
  * 若 `M.R rown colm ≠ 0`，则可以在此位置作为主元进行消元：调用 `nextA = gaussian_elimination_step_row M rown colm h` 执行行消元（**实现上复用了行消元的步骤**，实际上此处期望执行列方向的消元，但代码直接对行操作，然后因为后续策略有所不同，仍达成列消元效果），消去该行右侧所有元素？*(注意：这里逻辑稍复杂，因为按列消元预期应该消去同行右侧元素，但代码使用了行消元函数，可能存在误命名或逻辑问题。不过总之，nextA 更新了矩阵。)* 然后递归调用下一步：`row+1` 和 `col+1`。
* 终止条件同样是遍历完整矩阵或到达矩阵边缘。

总的来说，`gaussian_elimination_col_aux` 尝试以列为主来消元：遇到零主元则下移行，遇到非零则同时推进到下一列。

#### `gaussian_elimination_col`（按列高斯消元接口）

定义：`gaussian_elimination_col M` 执行列方向的梯形化消元。实现方法是**借助转置**：

* 若矩阵非空 (n, m > 0)，则对原始 `Gaussian M` 先取转置 `M.transpose`，然后对转置后的结构调用 `gaussian_elimination_col_aux` 从第0行第0列开始按行消元（相当于对原矩阵按列消元），最后对结果再次转置 `( ... ).transpose` 返回。
* 若矩阵为空则直接返回 `M`。

通过这种先转置再行消元再转置回来的技巧，实现了对原矩阵的列消元操作，使得结果矩阵 `R` 变为列梯形形式。

#### `firstNonZeroIndex`（第一个非零索引）

定义：`firstNonZeroIndex u i` 在一个行向量（函数 `u: Fin m → α`）中，从索引 `i` 开始向右查找第一个非零元素的位置，返回 `Option (Fin m)`（若找不到返回 `none`）。实现利用了列表的 `.find?` 方法：对`(finRange m).rtake (m - i)`从第`i`列开始的所有列，查找满足 `u idx ≠ 0` 的第一个索引。
用法：给定一行，从某起始列寻找第一个非零元素的位置，可用于在消元完成后寻找主元所在列。

#### `findNonZeroIndex`（寻找非零元素位置）

定义：`findNonZeroIndex u i j` 在矩阵 `u` 中，从第 `i` 行、第 `j` 列出发，寻找某个非零元素并返回其行列索引 `(row, col)`（类型为 `Fin n × Fin m`）。具体策略：

* 它先在第 `i` 行从列 `j` 开始调用 `firstNonZeroIndex (u i) j`，得到当前行往右的第一个非零列 `col`（若不存在则默认为 `j`）。
* 然后在第 `j` 列从行 `i` 开始调用 `firstNonZeroIndex (fun k => u k j) i`，得到当前列往下的第一个非零行 `row`（若不存在则默认为 `i`）。
* 返回 `(row, col)` 作为找到的非零位置。如果矩阵在 `(i,j)` 这行和这列都有非零项，这个函数并没有综合两者，而是简单地取当前行和当前列分别找到的结果组合成一个坐标。*(因此可能存在非最优选择，但足以用来找到某个非零候选主元。)*

#### `gaussian_elimination_step_final`（最终调整一步）

定义：`gaussian_elimination_step_final M i j` 在高斯消元最后阶段，对尚未处理的子矩阵进行调整，确保第 `i` 行、第 `j` 列处尽可能有一个非零主元：

* 调用 `z = findNonZeroIndex M.R i j` 找到从当前行和列开始的某个非零元素位置。
* 如果找到的位置正好就是 `(i, j)`，则无需调整，返回原 `M`。
* 如果找到的 `z.1 = i`（非零元素在同一行的右侧某列），则通过交换列将非零元素移到第 `j` 列：

  * 更新 `R := swap_cols M.R z.2 j` 交换该非零元素所在列 `z.2` 与当前第 `j` 列，
  * 相应地对 `Q` 也执行相同的列交换 `Q := swap_cols M.Q z.2 j`（保证整体等式关系保持）。
  * `P` 和 `M` 不变。
* 如果找到的 `z.1 ≠ i`（说明同列下方某行有非零值，在第 `j` 列的下方），则通过交换行将非零元素移到第 `i` 行：

  * 更新 `P := swap_rows M.P z.1 i` 交换找到的非零元素所在行 `z.1` 与当前行 `i`，
  * 更新 `R := swap_rows M.R z.1 i` 交换矩阵对应的两行。
  * `Q` 和 `M` 保持不变。
    调整后，在当前位置 `(i,j)` 就有了一个非零主元（通过列或行交换得到）。注意这一步可能仅进行行或列交换一次，确保对角线处尽可能出现非零。

#### `gaussian_elimination_final_aux`（最终高斯消元递归过程）

定义：`gaussian_elimination_final_aux M idx h` 完成高斯消元的最后整理阶段的递归函数。它尝试将矩阵进一步调整到秩的标准形：沿主对角线安放主元。过程：

* 输入：当前 `Gaussian M`，以及当前处理的对角线索引 `idx`（自然数），`h` 证明 `idx < n` 且 `idx < m`。
* 计算 `nextM = gaussian_elimination_step_final M ⟨idx, h.1⟩ ⟨idx, h.2⟩`，在位置 `(idx, idx)` 通过行或列交换放置一个非零元素作为主元（若可能）。
* 若 `idx < n-1` 且 `idx < m-1`（还未到最后一行或最后一列），则递归处理下一个对角线索引：调用 `gaussian_elimination_final_aux nextM (idx + 1) ...`。
* 若达到矩阵边界或处理完所有对角线位置，则返回 `nextM`。

这个递归每次把第 `idx` 行和第 `idx` 列的主元调整好，然后 `idx` 增1。递归终止度量是 `min(n, m) - idx`，表示还需要处理的对角元个数，保证最终会结束。

#### `gaussian_elimination_final`（最终高斯消元接口）

定义：`gaussian_elimination_final M` 完成最后的主元整理：

* 如果矩阵非空，则调用 `gaussian_elimination_final_aux M 0 h` 从对角线第0个开始调整，一直处理到所有可能的对角线位置都放置好主元为止；
* 如果矩阵为空则直接返回。
  经过此步骤，矩阵 `R` 将被调整成一种“准对角形”，即前若干个对角线上有非零（对应矩阵的秩），并且这些非零以外的其他位置都为0。这非常接近标准形。

#### `gaussian_elimination`（高斯消元完整流程）

定义：`gaussian_elimination M` 将前述三个阶段串联起来，对给定的 `Gaussian M` 执行完整的高斯消元算法：

1. **行梯形化**：先调用 `gaussian_elimination_row M`，得到 `R` 为行梯形形态。
2. **列梯形化**：再将结果传入 `gaussian_elimination_col`，进一步整理，使得列上也梯形化（这一阶段通常配合第一阶段可得到更简洁的形状）。
3. **主元对角整理**：最后调用 `gaussian_elimination_final`，把主元移到对角线上，形成标准的秩分块形式。

该函数最终返回的 `Gaussian` 结构中，`R` 矩阵将被化为**秩标准形**（即左上角是一个 `rank x rank` 的非零块，通常可化为单位阵，其余均为0）。

#### `Gaussian.init`（Gaussian 初始化）

定义：`Gaussian.init A` 接受一个矩阵 `A`，构造初始的 `Gaussian` 结构：

* 取 `P = 1`（恒等矩阵 `I_n`），
* `Q = 1`（恒等矩阵 `I_m`），
* `R = A`（初始结果矩阵就是原矩阵本身），
* `M = A`（原矩阵）。
  此时不做任何行列变换，保证 `P * M * Q = A` 显然成立。`Gaussian.init` 常用于将普通矩阵提升为消元算法所需的结构形式，以便后续调用 `gaussian_elimination` 处理。

#### `rankStdBlock`（秩标准块矩阵）

定义：`rankStdBlock K m n r` 返回一个规模为 `m × n`，域（或环）`K`上的标准秩矩阵。矩阵定义为：

* 当 `(i < r 且 j < r 且 i = j)` 时，该位置元素为1（在左上角 `r×r` 范围内放置1的对角线）；
* 其他情况下元素为0。
  这样得到的矩阵具有秩 `r`，且呈现出标准化的块状形式：前 `r` 个对角线上为 1，其余无论是该 `r×r` 块的非对角元素还是整个矩阵其他部分均为0。这个矩阵可视为秩为 `r` 的“标准形”（即 $\[I\_r, 0; 0, 0]\$）。

*(示例：代码最后通过 `gaussian_elimination (Gaussian.init A)` 测试了若干矩阵，并打印出 `P, R, Q` 矩阵验证结果满足 `P * A * Q = R`。此外，多处使用了 `#eval` 来演示各步骤函数的作用。)*

### Classification 部分（秩等价与分类）

#### `rankEquiv`（秩等价关系）

定义：`rankEquiv A B` 表示矩阵 `A` 和 `B` 是**秩等价**的，亦即存在可逆矩阵（元素在域/环 `K` 上）：`P ∈ GL(Fin m, K)`（`m×m`可逆矩阵）和 `Q ∈ GL(Fin n, K)`（`n×n`可逆矩阵），使得 \$B = P^{-1} A Q^{-1}\$，通常写成 \$B = P \* A \* Q\$（注意这里 Lean 定义中 `P.1` 表示提取矩阵，省略逆矩阵符号是因为直接给出的是逆的矩阵）。换言之，可以通过一系列初等行变换（对应左乘 \$P\$）和初等列变换（对应右乘 \$Q\$）将 \$A\$ 转换成 \$B\$。

#### `rankEquiv_iff_rank_eq`（秩等价当且仅当秩相等）

定理：`rankEquiv A B ↔ rank A = rank B`。也就是**矩阵秩等价当且仅当它们的秩相等**。这个命题说明，两矩阵如果能通过可逆的行列变换互相得到，那么它们一定有相同的秩；反之，若秩相同，在域上也总能找到把一个变成另一个的可逆变换。 *(代码中此定理标记为未完成 `sorry`，需证明。)*

#### `rankEquiv_setoid`（秩等价关系的等价关系实例）

定义：将上述 `rankEquiv` 注册为一个等价关系（`Setoid`）在矩阵集合上。这意味着：

* 自反性：任何矩阵 `A` 与自身秩等价（取 \$P = Q = I\$）。
* 对称性：若 `A` 秩等价于 `B`，则 `B` 秩等价于 `A`（因为可逆矩阵存在逆运算可互相转换）。
* 传递性：若 `A` 秩等价于 `B`，`B` 秩等价于 `C`，则 `A` 秩等价于 `C`（通过组合 \$P, Q\$ 矩阵实现）。
  Lean中用 `Setoid` 来表示等价关系，从而可以在矩阵按秩等价分类时使用商集等工具。*(此处证明过程略，代码中用 `sorry` 占位。)*

#### `rankEquiv_to_rankStdBlock`（秩等价到秩标准块）

定理：对于域（Field）上的任意矩阵 `A`，存在 `P ∈ GL(m, K)` 和 `Q ∈ GL(n, K)`，使得
$P * A * Q = \text{rankStdBlock}\ K\ m\ n\ (\text{rank}\ A).$
也就是说，任意矩阵都秩等价于一个“秩标准块矩阵”，其左上角是大小为 `rank A` 的单位阵块，其余为0。这证明了**秩标准形**的存在性：通过适当的可逆行、列变换，可以将矩阵转换成一个非常简单的形状，而这个形状清楚地体现了矩阵的秩。 *(该定理需要借助高斯消元过程的正确性来证明，代码中目前留为 `sorry`。)*

### Row 部分（行空间）

#### `rowSpace_left_mul_invariant`（左乘不变行空间）

定理：对于可逆矩阵 `P`（属于 `GL(Fin m, K)`）和任意矩阵 `A`（`m×n`），有
$\operatorname{span}_K(\text{range}(P * A)) = \operatorname{span}_K(\text{range}(A)).$
这表示**左乘可逆矩阵不会改变矩阵的行空间**。直观解释：`P * A` 相当于对 `A` 的行进行线性组合变换（因为左乘会线性组合行），但由于 `P` 可逆，这种组合是可逆的，不会改变行向量张成的子空间。证明需要利用可逆矩阵的性质和子空间等概念，代码中暂留 `sorry`。

#### `rowSpace_gauss_invariant`（高斯消元不变行空间）

定理：对任意矩阵 `M`，行高斯消元过程不会改变其行空间。形式化表述：
```lean
\operatorname{span}_K(\text{range}((\text{gaussian_elimination_row}\ M).R)) = \operatorname{span}_K(\text{range}(M.R)).
```
也就是说，`M` 通过高斯行消元得到的结果矩阵（我们关注其 `R`）的行向量所张成的空间，与原矩阵行向量张成的空间相同。高斯消元只对行进行初等变换，这些变换不会改变行向量的线性相关关系，因此秩和行空间保持不变。*(代码中此定理也留为 `sorry`，需要根据高斯消元的具体行操作来证明这一点，与上一条定理是呼应的。)*

### RankNormalForm 部分（秩规范形）

#### `Matrix.exists_rank_normal_form`（存在秩规范形）

定理：对于任意矩阵 `A : Matrix (Fin m) (Fin n) K`（`K`为交换环），存在可逆矩阵 `P ∈ GL(m, K)` 和 `Q ∈ GL(n, K)`，使得矩阵 \$B = P \* A \* Q\$ 满足：

* 若 `(i < \text{rank}(A) ∧ j < \text{rank}(A) ∧ i = j)`，则 \$B\_{i j} ≠ 0\$（在 \$B\$ 的秩范围内，对角线上的元素非零）；
* 否则，\$B\_{i j} = 0\$。

简单来说，就是存在一种变换可以把 `A` 化为一个“秩规范形”矩阵 \$B\$：这个 \$B\$ 在一个 \$r = \text{rank}(A)\$ 大小的正方子矩阵范围内，对角线上元素非零（通常可以选取为1，但此处只要求非零就行），除此之外其它位置全部为0。这个定理是前一条秩标准块存在性的更一般表述，不要求基域是域，仅需交换环，所以非零对角元不一定是1。*(证明思路通常基于高斯消元存在性和一般线性代数理论，代码中留 `sorry` 待证。)*

#### `Matrix.exists_rank_standard_form`（存在秩标准形）

定理：对于域 `K` 上的矩阵 `A`，存在可逆矩阵 `P ∈ GL(m, K)` 和 `Q ∈ GL(n, K)`，使得
$P * A * Q = \text{rankStdBlock}\ K\ m\ n\ (\text{rank}\ A).$
这其实与前述 `rankEquiv_to_rankStdBlock` 是同一命题，即**存在将矩阵转换为秩标准块形式的可逆变换**。区别在于这里明确以定理形式给出，并限定在域上，此时可以把对角线非零选为1，从而得到标准的单位阵块形式。这个定理直接展示了秩规范形可以取特殊形式（对角全1的标准形）。*(证明亦需高斯消元或秩分解理论支持，代码中留空 `sorry`。)*

### LU 部分

#### `Matrix.exists_LU_decomposition`（存在LU分解）

定理：对于任意 `n × n` 的矩阵 `A`（方阵）在环 `K` 上，存在：

* 一个置换 \$\sigma ∈ \text{Perm}(\Fin n)\$（对 `Fin n` 的一个排列），对应一个**置换矩阵** `permMatrix K σ` 表示行交换，
* 一个下三角矩阵 `L`（满足 `L.BlockTriangular id`，这里 `BlockTriangular id` 表示主对角线以下全是非零块、以上为0——即下三角矩阵），且要求 `∀ i, L_{i,i} = 1` （`L` 主对角线元素全为1，即单位下三角矩阵形式），
* 一个上三角矩阵 `U`（满足 `U.BlockTriangular (-id)`，`-id` 表示上三角的形状），

使得经过行置换的矩阵等于它们的乘积：
$(\text{permMatrix}\ K\ σ) * A = L * U.$
这正是**LU 分解**（列主元高斯消元的结果）的存在性表述：任意矩阵（在一定条件如主元存在的情况下）可以分解为一个置换矩阵、一个下三角单位矩阵和一个上三角矩阵的乘积。置换矩阵对应在消元中可能需要交换行（partial pivoting）的情况。该定理证明了LU分解在一般环上的存在（需要某些条件如可交换等，代码中基于Ring假设并留 `sorry` 待证）。

---

**补充说明**：以上内容涵盖了代码各部分定义的函数和定理，以及它们的用途和含义。此外，代码中使用了一些 Lean **战术（tactic）** 和概念：

* `simp`：一种自动化简化战术。例如在证明 `P * M * Q = R` 时用 `by simp` 即可解决（因初始 `P`、`Q`是单位矩阵，使等式成立）。
* `rw [...]`：重写战术，用所给等式（如 `tsub_lt_tsub_iff_left_of_le`）改写当前目标。在终止证明中用于处理减法不等式。
* `linarith`：线性算术战术，可自动证明线性不等式目标。在递归终止证明中用它来证明计数 `(n+m) - (row+col)` 的严格递减。
* `termination_by ...` / `decreasing_by`：用于定义递归函数时显式指定递归度量和证明其单调递减，确保函数终止。

Lean 中还涉及一些概念：

* `NeZero n`：类型类，表示自然数 `n` 非零（这样 `Fin n` 类型才非空，便于避免零维矩阵情况）。
* `LinearOrder α`：类型类，表示元素类型 `α` 上有线性次序，用于比较主元大小。常配合一个绝对值函数 `abs` 实现选取“最大”元素。
* `GL (Fin m) K`：一般线性群，表示所有在 `Fin m` 上的可逆矩阵（`m×m` 方阵）集合，`P ∈ GL(Fin m, K)`意味着 `P` 是一个 `m×m` 可逆矩阵。
* `permMatrix K σ`：将一个排列 `σ` 转换为对应的置换矩阵（对角线按 `σ` 重新排列的0-1矩阵），左乘矩阵相当于对行按照 `σ` 进行重排。
* `BlockTriangular f`：矩阵形状性质，`id` 通常指下三角（本例 `L`），`-id` 指上三角（本例 `U`）。具体而言，`L.BlockTriangular id` 表示如果行索引 < 列索引则该元素为0（下三角），`U.BlockTriangular (-id)` 表示行索引 > 列索引则元素为0（上三角）。
* `span K (range A)`：`A` 的行空间，即矩阵 `A` 所有行向量的线性组合张成的子空间。`range A` 在 Lean 中表示将矩阵视为函数后所有行得到的列表（或集合）。行空间不变性的定理都建立在这个概念上。
* `rank A`：矩阵的秩，通常定义为行空间的维度（或列空间维度）。代码中假定已有 `rank` 函数可用。秩等价关系和标准形都是围绕 `rank A` 来描述的。
* 初等变换：本代码通过 `swap_rows`/`swap_cols`（行列交换）、`scale_row`（行数乘非零标量）、`add_row_multiple`（行加倍）等函数实现矩阵的行初等变化。列初等变化可对应类似的操作。高斯消元正是反复应用这些初等变化实现矩阵变换。

综上，代码各部分协同实现了高斯消元算法，证明了秩的不变性和标准形存在等理论命题，并提供了LU分解存在性的证明思路。以上总结以分段方式概括了每个定义和定理的名称、用途和含义，方便读者快速了解代码功能和数学意义。

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


## 高斯消元lean4源代码
```lean
import Mathlib

variable {α : Type*}

open Matrix Equiv Nat List

section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)

def swap_rows  (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix (swap i j : Perm (Fin n)) id

def swap_cols  (i j : Fin m) : Matrix (Fin n) (Fin m) α :=
   (swap_rows M.transpose i j).transpose

def gaussian_update [Add α] [Mul α] [Sub α]
    (i k : Fin n) (a b : α) : (Fin m) → α :=
  if k ≤ i then M k else a • M k - b • M i

def gaussian_update_row [Add α] [Mul α] [Sub α]
  (i : Fin n) (j : Fin m):
  Matrix (Fin n) (Fin m) α :=
  fun k => gaussian_update M i k (M i j) (M k j)

end Basic

structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * M * Q = R
  -- P M Q = [I_r, 0;
            -- 0, 0]

def Gaussian.transpose {n m α}[Ring α](M : Gaussian n m α) : Gaussian m n α where
  P := M.Q.transpose
  R := M.R.transpose
  Q := M.P.transpose
  M := M.M.transpose
  hm := by
    rw [← M.hm]
    sorry

section Gauss


variable {n m} [Ring α] (M : Gaussian n m α) [NeZero n] [NeZero m]

def find_pivot_col [LinearOrder α] (M : Fin n → α) (i : Fin n): Fin n :=
  (argmax (abs ∘ M) ((finRange n).rtake (n - i))).getD 0

-- 目前进行到(i,j)，接下来选取按行来消元
def gaussian_elimination_step_row (i : Fin n) (j : Fin m)
    : Gaussian n m α where
  P := fun k => gaussian_update M.P i k (M.R i j) (M.R k j)
  R := gaussian_update_row M.R i j
  Q := M.Q
  M := M.M
  hm := by
    funext k
    simp only [gaussian_update, gaussian_update_row, Matrix.mul_apply_eq_vecMul,
      Matrix.vecMul_vecMul, ← M.hm]
    split_ifs with h_le
    simp
    simp [sub_vecMul, Matrix.vecMul_smul, Matrix.vecMul_smul]


-- 目前进行到(i,j)，接下来选取列主元
def gaussian_elimination_pivot_row [LinearOrder α] (i : Fin n) (j : Fin m) :
    Gaussian n m α :=
  -- 取出第j列，从第i行开始的最大元素的下标
  let z := (find_pivot_col (fun k => M.R k j) i)
  -- 如果最大元素的下标和本身一样，。。。
  if z = i then M
  else
    {
    P := swap_rows M.P z i
    R := swap_rows M.R z i
    Q := M.Q
    M := M.M
    hm := sorry
    }

def gaussian_elimination_row_aux [LinearOrder α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  let pivotA := gaussian_elimination_pivot_row M rown colm

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if h : pivotA.R rown colm = 0 then
      gaussian_elimination_row_aux pivotA row hr (col + 1) (add_lt_of_lt_sub ht.2)

    else
      let nextA := gaussian_elimination_step_row pivotA rown colm
      gaussian_elimination_row_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    pivotA

def gaussian_elimination_row [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_row_aux M 0 h.1 0 h.2
  else M

def gaussian_elimination_col_aux [LinearOrder α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if h : M.R rown colm = 0 then gaussian_elimination_col_aux M (row + 1) (add_lt_of_lt_sub ht.1) col hc
    else
      let nextA := gaussian_elimination_step_row M rown colm
      gaussian_elimination_col_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    M

def gaussian_elimination_col [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then (gaussian_elimination_col_aux M.transpose 0 h.2 0 h.1).transpose
  else M

def firstNonZeroIndex [DecidableEq α] (u : Fin m → α) (i : Fin m):
    Option (Fin m) :=
  ((finRange m).rtake (m - i)) |>.find? (fun i => u i ≠ 0)

def findNonZeroIndex [DecidableEq α] (u : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) :
    Fin m := (firstNonZeroIndex (u i) j).getD j

def gaussian_elimination_step_final [LinearOrder α] (i : Fin n) (j : Fin m) :
    Gaussian n m α :=
  -- 取出第j列，从第i行开始的不为0的下标
  let z := findNonZeroIndex M.R i j
  -- 如果下标和本身一样，。。。
  if z = j then M
  else
    {
      P := M.P
      R := swap_cols M.R z j
      Q := swap_cols M.Q z j
      M := M.M
      hm := sorry
    }

def gaussian_elimination_final_aux [LinearOrder α] (M : Gaussian n m α)
    (idx : ℕ) (h : idx < n ∧ idx < m) :
    Gaussian n m α :=
  let nextM := gaussian_elimination_step_final M ⟨idx, h.1⟩ ⟨idx, h.2⟩
  if ht : (idx < n - 1) ∧ (idx < m - 1) then
    gaussian_elimination_final_aux nextM (idx + 1) ⟨add_lt_of_lt_sub ht.1, add_lt_of_lt_sub ht.2⟩
  else
    nextM
termination_by min n m - idx

def gaussian_elimination_final [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_final_aux M 0 h
  else M

def gaussian_elimination [LinearOrder α] : Gaussian n m α :=
  gaussian_elimination_final <| gaussian_elimination_col <| gaussian_elimination_row M

def Gaussian.init (A : Matrix (Fin n) (Fin m) α) : Gaussian n m α :=
    ⟨1, A, 1, A, by simp⟩

#check Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
#eval! gaussian_elimination
  (Gaussian.init !![1, 2, (3 : ℤ), 4 ;
                    1, 2, (5 : ℤ), 6 ;
                    1, 2, (7 : ℤ), 8 ])
#eval !![1, 0, 0; -1, 0, 1; -2, 4, -2] * !![1, 2, 3, (4 : ℤ); 1, 2, 5, 6; 1, 2, 7, 8] * !![1, -3, -2, -4; 0, 0, 1, 0; 0, 1, 0, -4; 0, 0, 0, 4]
def rankStdBlock (K : Type*) [Zero K] [One K]
    (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < r ∧ (j : ℕ) < r then
            if (i : ℕ) = j then 1 else 0
          else 0

end Gauss

section Classification

variable {K : Type*} [CommRing K]
variable {m n : ℕ}

def rankEquiv (A B : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K), B = P.1 * A * Q.1

theorem rankEquiv_iff_rank_eq (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B ↔ rank A = rank B := by sorry

instance rankEquiv_setoid : Setoid (Matrix (Fin m) (Fin n) K) where
 r := rankEquiv
 iseqv := sorry

theorem rankEquiv_to_rankStdBlock [Field K] (A : Matrix (Fin m) (Fin n) K) :
    rankEquiv A (rankStdBlock K m n A.rank) := by sorry

end Classification

section Row

open Submodule Set
variable {K : Type*} [CommRing K]
variable {m n : ℕ}

theorem rowSpace_left_mul_invariant
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
    span K (range (P.1 * A)) = span K (range A) := by
  sorry

theorem rowSpace_guass_invariant [NeZero n] [NeZero m] [LinearOrder K] (M : Gaussian n m K) :
    span K (range (gaussian_elimination_row M).R) = span K (range M.R) := by
  sorry

end Row

section RankNormalForm

variable {m n : ℕ} {K : Type*}  (A : Matrix (Fin m) (Fin n) K)

theorem Matrix.exists_rank_normal_form [CommRing K] [NoZeroDivisors K] :
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
            (P.1 * A * Q.1) i j ≠ 0
          else (P.1 * A * Q.1) i j = 0 := by
  sorry

#checkBasis.SmithNormalForm
theorem Matrix.exists_rank_standard_form [Field K]:
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      P.1 * A * Q.1 = rankStdBlock K m n A.rank := by
  sorry

end RankNormalForm

section LU

open Equiv Equiv.Perm
variable {K : Type*} [Field K]

#check Matrix.BlockTriangular
#check Equiv.Perm.permMatrix

theorem Matrix.exists_LU_decomposition
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ (σ : Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) K),
      L.BlockTriangular id   ∧
      U.BlockTriangular (-id) ∧
      (∀ i, L i i = 1) ∧
      (permMatrix K σ) * A = L * U := by
  sorry

end LU

section Fullrankfactorization

variable {K : Type*} [CommRing K]

theorem exists_fullRank_factorization {m n}
    (A : Matrix (Fin m) (Fin n) K) :
    ∃ (B : Matrix (Fin m) (Fin A.rank) K) (C : Matrix (Fin A.rank) (Fin n) K),
    A = B * C := by sorry

end Fullrankfactorization
```


