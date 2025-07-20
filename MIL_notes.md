# MIL

## C02_Basics

### Tactics 用法索引

| 中文名称       | tactic 名称       | 简要说明 |
|----------------|------------------|----------|
| 重写           | `rw`             | 使用等式、等价命题等进行目标/假设重写 |
| 结合律重写     | `rw [add_assoc]` | 应用于加法结合律 `(a + b) + c = a + (b + c)` |
| 使用定理证明目标 | `apply`         | 试图使用某个定理证明当前目标 |
| 引入中间命题   | `have`           | 在上下文中引入一个中间命题及其证明 |
| 精确应用定理   | `exact`          | 精确提供一个项（定理、等式等）来满足当前目标 |
| 对称变换       | `symm`           | 将目标 a = b 转为 b = a |
| 用定理完成目标 | `apply 定理名`   | 直接使用指定定理 |
| 简化数值       | `norm_num`       | 化简数值表达式（如 1 + 1 = 2） |
| 定义改写       | `rw [sub_eq_add_neg]` | 使用减法定义 `a - b = a + -b` |
| 组合目标引理   | `rw [← add_assoc]` 等 | 各种组合多步重写 |
| 嵌套结构引理引入 | `have h := by rw [...]` | 先声明一个引理，再在子块中使用 tactic 证明 |


### 公式（定理）使用索引

| 中文名称           | Lean 名称                 | 定理定义 |
|--------------------|---------------------------|-----------|
| 加法结合律         | `add_assoc`               | `(a + b) + c = a + (b + c)` |
| 零加等于本身       | `add_zero`                | `a + 0 = a` |
| 零乘等于零         | `zero_mul`                | `0 * a = 0` |
| 乘法分配律（加法左分配） | `add_mul`            | `(a + b) * c = a * c + b * c` |
| 乘法分配律（加法右分配） | `mul_add`            | `a * (b + c) = a * b + a * c` |
| 加法逆元消去       | `add_neg_cancel`          | `a + -a = 0` |
| 加法右逆元消去     | `add_neg_cancel_right`    | `a + b + -b = a` |
| 加法左逆元消去     | `neg_add_cancel`          | `-a + a = 0` |
| 加法左消去         | `add_left_cancel`         | `a + b = a + c → b = c` |
| 加法右消去         | `add_right_cancel`        | `a + b = c + b → a = c` |
| 等于零推出相反数等于对方 | `neg_eq_of_add_eq_zero` | `a + b = 0 → -a = b` |
| 等于零推出自身等于负对方 | `eq_neg_of_add_eq_zero` | `a + b = 0 → a = -b` |
| 零的相反数等于零   | `neg_zero`                | `-0 = 0` |
| 双重相反等于本身   | `neg_neg`                 | `-(-a) = a` |
| 减自身等于零       | `self_sub`                | `a - a = 0` |
| 1+1=2              | `one_add_one_eq_two`      | `1 + 1 = 2` |
| 2*a = a + a        | `two_mul`                 | `2 * a = a + a` |
| 乘法单位元左单位   | `one_mul`                 | `1 * a = a` |
| 乘法单位元右单位   | `mul_one`                 | `a * 1 = a` |
| 乘法结合律         | `mul_assoc`               | `(a * b) * c = a * (b * c)` |
| 左乘逆元消去       | `inv_mul_cancel`          | `a⁻¹ * a = 1` |
| 右乘逆元消去       | `mul_inv_cancel`          | `a * a⁻¹ = 1` |
| 逆元乘积的逆       | `mul_inv_rev`             | `(a * b)⁻¹ = b⁻¹ * a⁻¹` |

---

### 常见符号速查

| 符号     | VSCode 输入法        | 含义 |
|----------|----------------------|------|
| `→`     | `\to` or `\r`        | 蕴含符号 |
| `↔`     | `\iff` or `\lr`      | 等价符号 |
| `∀`     | `\all` or `\fa`      | 全称量词 |
| `∃`     | `\ex`                | 存在量词 |
| `∧`     | `\and`               | 合取（与） |
| `∨`     | `\or`                | 析取（或） |
| `¬`     | `\not`               | 否定 |
| `⊢`     | `\vdash`             | “需要证明” |
| `≠`     | `\ne`                | 不等于 |



# Real 分析练习所用 tactic 与公式中文索引

## ✦ 一、Tactics 用法索引

| 中文名称         | tactic 名称             | 用法说明 |
|------------------|--------------------------|----------|
| 使用定理         | `apply 定理名`           | 使用一个已知定理来变换目标 |
| 精确使用定理     | `exact 定理名`           | 精确提供某个定理/表达式作为目标的证明 |
| 链式推理         | `calc`                   | 构造链式等式/不等式推理 |
| 自动不等式判断   | `linarith`               | 使用线性不等式自动化 |
| 引理先赋值再使用 | `have h := by ...`       | 在上下文中声明中间引理 |
| 简单数值计算     | `norm_num`               | 数值型目标的化简，如 `0 < 2` |
| 构造合取目标     | `constructor`            | 构造如 `P ∧ Q` 的目标 |
| 重写             | `rw [定理名]`            | 将目标或上下文使用定理改写 |
| 使用目标转换     | `apply 定理 at 目标`     | 对目标或某个假设进行变换 |

---

## ✦ 二、数学分析中用到的定理公式

| 中文名称                   | Lean 名称                    | 定理定义 |
|----------------------------|-------------------------------|-----------|
| 指数函数的单调性           | `exp_le_exp`                 | `a ≤ b ↔ exp a ≤ exp b` |
| 指数函数恒正               | `exp_pos a`                  | `0 < exp a` |
| 对数函数的保序性           | `log_le_log`                 | `0 < a → a ≤ b → log a ≤ log b` |
| 加法对不等式保序（左加）   | `add_le_add_left`            | `a ≤ b → c + a ≤ c + b` |
| 函数复合的保序性           | `lt_of_le_of_lt`             | `a ≤ b ∧ b < c → a < c` |
| 严格小于的传递性           | `lt_trans`                   | `a < b ∧ b < c → a < c` |
| 减法对不等式的保序性       | `sub_le_sub_left`            | `b ≤ a → c - a ≤ c - b` |
| 绝对值小于等价于夹在正负之间 | `abs_le'.mpr`               | `(x)abs ≤ y ↔ -y ≤ x ∧ x ≤ y` |
| 平方恒非负                 | `pow_two_nonneg`             | `∀ x, 0 ≤ x ^ 2` |
| 完全平方公式               | `ring` 推理中自动展开        | `a^2 ± 2ab + b^2 = (a ± b)^2` |
| 除法不等式乘除转换         | `le_div_iff₀`                | `c > 0 → a ≤ b / c ↔ a * c ≤ b` |

---

## ✦ 三、例子概览与策略亮点

| 例子描述                           | 使用亮点策略           |
|------------------------------------|-------------------------|
| `a ≤ b → c - exp b ≤ c - exp a`    | 使用 `sub_le_sub_left` 与 `exp_le_exp.mpr` |
| `log(1 + exp a) ≤ log(1 + exp b)` | 构造严格正数条件，再用 `log_le_log` |
| `(a*b)abs ≤ (a² + b²)/2`              | 使用两个辅助引理 (`fact1` 和 `fact2`) 再配合 `abs_le'.mpr` 构造 |




mp/mpr:

如果一个定理是 a `\iff` b, 那么a `\to` b 用定理名称.mp


对于一个prop类型，如果里面涉及（h：假设） p `\iff` q, 那么可以使用re [p_q h] 来使用这个 `\iff`

have h : (0 : ℝ) < 2 := by norm_num

对于这种东西存在的意义就是，某个运用的条件需要提前备案，这种思想，就是当我们要使用某个引理/定理/定义的时候，我们要检查这个条件是否备案，或者是否显然，我们都应该将其备案，方便我们投喂

open 语句是用来“打开”一个命名空间（namespace），使得该命名空间中的定义（定理、函数、常量等）可以直接访问而不用写前缀

因为 open 只是一个局部设置，不需要 end 来封闭。它不是一个 block 结构（比如 namespace 是），也不是 section。你可以在任意地方写 open xxx，它影响的是之后的可见范围。

split_ands 是一个 Mathlib 的 tactic（不是 Lean 核心的），功能是：
如果目标是多个「∧」构成的复合合取，比如 A ∧ B ∧ C，它会自动拆分成多个子目标（类似 constructor; constructor; constructor），而你只需写一行。 constructor是lean的核心


对于 `\or` 的结构，可以用left 或者 right 来指定左右，如果只想指定左边，直接constructor也可以。

`nlinarith` 擅长非线性，涉及平方项，乘积等

`linarith` 擅长线性

`ring`  一行代码结束游戏，运用环的性质 一种“模仿 Gröbner 基技术”的风格方法

`ring_nf`化简表达式至标准形式	显式给出标准形式（normal form）	想要“展示/对比”标准化结果



### ✅ 一、Tactic 用法索引

| 中文名称             | tactic 名称             | 功能说明 |
|----------------------|--------------------------|----------|
| 应用定理             | `apply 定理名`           | 使用一个具体的定理或引理证明当前目标 |
| 反复应用 tactic      | `repeat`                 | 对后续的 tactic 多次重复应用 |
| 构造不等式链式证明   | `calc`                   | 构造清晰的链式推理 |
| 左边加右边的等式     | `rw [公式]`              | 将目标或假设按等式替换 |
| 添加辅助引理         | `have h := by ...`       | 引入一个中间步骤的引理 |
| 自动数值不等式化简   | `linarith`               | 自动处理线性不等式推理 |
| 化简减法             | `sub_add_cancel`         | 形式为 `a - b + b = a` 的恒等式 |
| 化简幂次             | `rw [pow_two]`           | 将 `x^2` 替换为 `x * x` |

---

### ✅ 二、实数不等式与代数恒等式定理索引

| 中文名称                 | Lean 名称                      | 公式定义或结论 |
|--------------------------|---------------------------------|----------------|
| 最小值不等式：左边       | `min_le_left a b`               | `min a b ≤ a` |
| 最小值不等式：右边       | `min_le_right a b`              | `min a b ≤ b` |
| 小于等于 min 的条件      | `le_min`                        | `c ≤ a ∧ c ≤ b → c ≤ min a b` |
| 最大值不等式             | `max_le`                        | `a ≤ c ∧ b ≤ c → max a b ≤ c` |
| 小于等于 max 的条件      | `le_max_left`, `le_max_right`   | `a ≤ max a b`, `b ≤ max a b` |
| 小于等于的传递性         | `le_trans`                      | `a ≤ b ∧ b ≤ c → a ≤ c` |
| 加法与不等式传递         | `add_le_add_right`              | `a ≤ b → a + c ≤ b + c` |
| 减法与加法互逆           | `sub_add_cancel`                | `a - b + b = a` |
| 加负数等于减法           | `sub_eq_add_neg`                | `a - b = a + (-b)` |
| 负数加法抵消             | `add_neg_cancel_right`          | `a + b - b = a` |
| 绝对值加法不等式         | `abs_add`                       | `|a + b| ≤ |a| + |b|` |
| 减法右抵消               | `add_sub_cancel_right`          | `a + b - b = a` |

---

### ✅ 三、整除与数论定理索引（ℕ）

| 中文名称                         | Lean 名称                        | 公式定义或结论 |
|----------------------------------|----------------------------------|----------------|
| 整除的传递性                     | `dvd_trans`                      | `x ∣ y ∧ y ∣ z → x ∣ z` |
| 整除乘法（左因子）               | `dvd_mul_left`                  | `x ∣ x * y` |
| 整除乘法（右因子）               | `dvd_mul_of_dvd_right`          | `x ∣ y → x ∣ y * z` |
| 整除乘法（两边整除）             | `dvd_mul_of_dvd_left`           | `x ∣ y → x ∣ x * y` |
| 整除加法                         | `dvd_add`                        | `x ∣ a ∧ x ∣ b → x ∣ a + b` |
| 自反整除                         | `dvd_rfl`                        | `x ∣ x` |
| 平方展开                        | `pow_two`                        | `x ^ 2 = x * x` |

---

### ✅ 四、最大公因数和最小公倍数定理索引（ℕ）

| 中文名称               | Lean 名称                   | 公式定义或结论 |
|------------------------|------------------------------|----------------|
| gcd 与 0 的右运算       | `Nat.gcd_zero_right`         | `gcd n 0 = n` |
| gcd 与 0 的左运算       | `Nat.gcd_zero_left`          | `gcd 0 n = n` |
| lcm 与 0 的右运算       | `Nat.lcm_zero_right`         | `lcm n 0 = 0` |
| lcm 与 0 的左运算       | `Nat.lcm_zero_left`          | `lcm 0 n = 0` |
| gcd 的左右可交换性     | `Nat.dvd_antisymm` + `Nat.dvd_gcd` 等 | `gcd a b = gcd b a` |

---

### ✅ 五、结构类比提示

- `min` 与 `gcd` 在结构上有相似性（都是“满足条件的最大/最小”），常用双向引理构造等式。
- `add_le_add_right` 与 `le_min` 常配合使用，构造复杂不等式。
- `abs_add` 与三角不等式密切相关，是常用绝对值不等式工具。


当你写 have h := abs_add (a - b) b 时，Lean 自动利用 abs_add 的类型和参数，通过类型推导得出结论类型是一个命题，并将其赋予 h，这一过程完全依赖 Lean 的 依赖类型理论机制（dependent type theory）。

如果你想深入理解这种机制，建议从：

类型论（Type Theory）

Curry–Howard 对应

Lean 的 elaboration/type class inference

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

    --这里面最大公约数的运算法则和min a b形成一个自然的同构


example: min m n = min n m := by

  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

## 📘 Lean 4：扩展实数 `EReal` 中的不等式与相关定理

---

### ✅ 基本不等式映射（`ℝ → EReal`）

| 中文名称             | Lean 名称                        | 表达式 / 意义 |
|----------------------|----------------------------------|----------------|
| 实数小于等价         | `EReal.coe_lt_coe_iff`           | `(x : EReal) < (y : EReal) ↔ x < y` |
| 实数小于等价别名     | `EReal.coe_lt_coe`               | 反向构造用法 |
| 实数小于等于等价     | `EReal.coe_le_coe_iff`           | `(x : EReal) ≤ (y : EReal) ↔ x ≤ y` |
| 实数小于等于别名     | `EReal.coe_le_coe`               | 反向构造用法 |
| 实数等号等价         | `EReal.coe_eq_coe_iff`           | `(x : EReal) = (y : EReal) ↔ x = y` |
| 实数不等等价         | `EReal.coe_ne_coe_iff`           | `(x : EReal) ≠ (y : EReal) ↔ x ≠ y` |
| 实数 ≥ 0 映射        | `EReal.coe_nonneg`               | `(0 : EReal) ≤ x ↔ 0 ≤ x` |
| 实数 ≤ 0 映射        | `EReal.coe_nonpos`               | `(x : EReal) ≤ 0 ↔ x ≤ 0` |
| 实数 > 0 映射        | `EReal.coe_pos`                  | `(0 : EReal) < x ↔ 0 < x` |
| 实数 < 0 映射        | `EReal.coe_neg'`                 | `(x : EReal) < 0 ↔ x < 0` |

---

### ✅ 与顶/底元素相关的不等式

| 中文名称              | Lean 名称                | 表达式 / 意义 |
|-----------------------|---------------------------|----------------|
| ⊥ 小于任意实数       | `EReal.bot_lt_coe`         | `⊥ < (x : EReal)` |
| 任意实数小于 ⊤       | `EReal.coe_lt_top`         | `(x : EReal) < ⊤` |
| 0 < ⊤                | `EReal.zero_lt_top`        | `(0 : EReal) < ⊤` |
| ⊥ < 0                | `EReal.bot_lt_zero`        | `⊥ < 0` |
| ⊤ ≠ 实数              | `EReal.coe_ne_top`, `top_ne_coe` | `(x : ℝ) ≠ ⊤` |
| ⊥ ≠ 实数              | `EReal.coe_ne_bot`, `bot_ne_coe` | `(x : ℝ) ≠ ⊥` |

---

### ✅ 不等式与实数值的比较（`toReal` 推出）

| 中文名称                      | Lean 名称                      | 表达式 / 意义 |
|-------------------------------|---------------------------------|----------------|
| `EReal.toReal = 0` 等价       | `EReal.toReal_eq_zero_iff`      | `x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥` |
| `EReal.toReal ≠ 0` 等价       | `EReal.toReal_ne_zero_iff`      | `x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥` |
| `toReal` 单调性（可提升）     | `EReal.toReal_le_toReal`        | 需要非顶非底前提：`x ≤ y → x.toReal ≤ y.toReal` |
| `EReal.toReal` 非负性推导     | `EReal.toReal_nonneg`           | `0 ≤ x → 0 ≤ x.toReal` |
| `EReal.toReal` 非正性推导     | `EReal.toReal_nonpos`           | `x ≤ 0 → x.toReal ≤ 0` |

---

### ✅ 等于顶 / 底 的逻辑刻画

| 中文名称               | Lean 名称                    | 表达式 / 意义 |
|------------------------|-------------------------------|----------------|
| 等于 ⊤ 的充要条件     | `EReal.eq_top_iff_forall_lt`  | `x = ⊤ ↔ ∀ r : ℝ, (r : EReal) < x` |
| 等于 ⊥ 的充要条件     | `EReal.eq_bot_iff_forall_lt`  | `x = ⊥ ↔ ∀ r : ℝ, x < (r : EReal)` |

---

### ✅ 不等式之间的稠密性（有理数 / 实数插值）

| 中文名称                       | Lean 名称                            | 表达式 / 意义 |
|--------------------------------|---------------------------------------|----------------|
| 存在实数介于两个 `EReal`      | `EReal.exists_between_coe_real`      | `x < z → ∃ y : ℝ, x < y ∧ y < z` |
| 存在有理数介于两个 `EReal`    | `EReal.exists_rat_btwn_of_lt`        | 同上，但 `y : ℚ` |
| 小于等价于存在有理数插值      | `EReal.lt_iff_exists_rat_btwn`       | `x < y ↔ ∃ r : ℚ, x < ↑r ∧ ↑r < y` |
| 小于等价于存在实数插值        | `EReal.lt_iff_exists_real_btwn`      | 同上，`r : ℝ` |

---

### ✅ 与 `ℝ≥0∞` 的关系（`ENNReal → EReal`）

| 中文名称                        | Lean 名称                             | 表达式 / 意义 |
|---------------------------------|----------------------------------------|----------------|
| 不等式保持单调                 | `EReal.coe_ennreal_le_coe_ennreal_iff` | `(x : EReal) ≤ (y : EReal) ↔ x ≤ y` |
| 小于关系保持                   | `EReal.coe_ennreal_lt_coe_ennreal_iff` | 同上，`<` |
| 正数等价（从 `ℝ≥0∞`）         | `EReal.coe_ennreal_pos_iff_ne_zero`    | `(0 : EReal) < x ↔ x ≠ 0` |
| 映射后非负                     | `EReal.coe_ennreal_nonneg`             | `(0 : EReal) ≤ (x : ℝ≥0∞)` |
| 映射后非负集等价              | `range ((↑) : ℝ≥0∞ → EReal) = Ici 0`   | 所有 `ℝ≥0∞` 嵌入 EReal 的值非负 |

---

### ✅ 结构补充说明

- `EReal` 是通过 `WithBot (WithTop ℝ)` 实现的拓展实数 `[-∞, +∞]`。
- 所有 `ℝ` 的嵌入都通过 `Real.toEReal : ℝ → EReal` 实现，并注册为 `[coe]`。
- 所有不等式定理都围绕嵌入的单调性 `coe_strictMono` 展开。



PartialOder: 偏序

  --NOTE：全序集：

     ∀ a, b, c, 有 a ≤ b 或 b ≤ a 或 a = b。/LinearOrder α

  -定义一种二元关系满足以下三种性质：
    -反自反性：对于任意a，a ≤ a
    -反对称性：对于任意a和b，如果a ≤ b，b ≤ a，则a = b（充要）
    -传递性：对于任意a,b,c，如果a ≤ b且b ≤ c，则a ≤ c

  -定义一个集合A，称为偏序集，如果它满足以下条件：
    -A中任意两个元素a和b，如果a ≤ b，则存在一个c，使得a ≤ c且c ≤ b
    -A中任意元素a，存在一个最小元素a*，使得∀b∈A，a* ≤ b
    -A中任意元素a，存在一个最大元素a*，使得∀b∈A，b ≤ a*

  -定义一个函数f，称为偏序函数，如果它满足以下条件：
    -f是二元函数
    -f(a) ≤ f(b)当且仅当a ≤ b
    -f(a) = f(b)当且仅当a = b或a ≤ b且b ≤ a

在 Lean 中，inf（∧，meet）默认优先级高于 sup（∨，join），这和数学中的通常习惯是一致的。

@+一个定理名字：禁止lean自动推导隐式参数，因为防止lean退错，这个时候必须要用填写所有参数，或者用_让lean自动推导。

加上@后，tactic的部分应用和全部应用：
        部分应用；@tactic_name _ _ (A) 那么返回的是一个关于A的函数
        全部应用；@tactic_name _ _ (A) (B) 那么AB可以正常按规则运行

        ==问题在于，为什么tactic可以实现部分应用，它的原理是什么？


variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]

--Lean 不会自动从 [IsStrictOrderedRing R] 中提取并注册它依赖的结构，所以你必须把 Ring R 和 PartialOrder R 显式声明在上下文中。


  `apply add_le_add_right`
  
   --如果apply后的子目标已经有证明了，直接加在后面，或者跳行exact它
  `exact h`

  或者   `apply add_le_add_right h`


`theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by`

这种有按先后顺序出现的隐式参数`a`和`b`的定理， aux1 _ _(传入a，b) h(再传入引理)

/-
距离函数dist(x,y)的定义：
    对于一个度量空间X，定义dist(x,y)为x和y之间的距离，满足以下性质：
        1. dist(x,y) ≥ 0
        2. dist(x,y) = 0 当且仅当x = y 在伪度量空间中不做要求

                   -一个 伪度量空间
                   -是一个集合 X
                   -上面定义了一个“距离函数” dist : X → X → ℝ

        3. dist(x,y) = dist(y,x)
        4. dist(x,z) ≤ dist(x,y) + dist(y,z)
-/

/-
《第二章要点总结

一个东西格（lattice），是因为它们在某种“偏序”结构下，对任意两个元素都存在最大下界（infimum ∧）和最小上界（supremum ∨）



1. calc关键字：
   以calc开头而不以by开头的表达式算是一个证明项  **编写calc可以先用sorry以确保lean先认可中间表达式**
   calc格式严格，下划线必须对齐                 **然后再进行证明**
   **lean使用缩进来确定calc还有tactic开始和结束的地方**

2. ring策略可以用 **import Mathlib.Data.Real.Basic** 导入 或者 **import Mathlib.Tactic**

3. 传入两个参数
          def mul : ℕ → ℕ → ℕ := fun x => fun y => x * y

          #eval (mul 3) 4  -- 输出 12

   柯里化是将多参数转化成**一系列每次只接受一个参数的函数的过程**

   为什么add_comm a b 可以，add_comm a 也可以，只不过这时候 <add_comm a> 变成一个还需要一个参数的函数（lean会自动推导出那个参数）

4. 在lean中，减法等于加上它的**加法逆元**，即：a - b = a + (-b)
    -实数的减法就是如此定义的

5. **apply?** 自动定理搜索工具

6. 在二元运算符前后习惯加上空格

7. **min** 在 **max** 上的分配律就跟乘法对加法的分配律一样

      example：min a max(b c) ≤ max( min a b, min a c )

      这是因为有统一的结构，和格理论有关。

8. 对于自然数次幂： 应用**dvd_mul_left**会强制把 x^2 展开为 x^1 * x

9. **⊓ \glb**  **⊔ \lub**  **⊓ \inf**  **⊔ \sup**

10. 一些格的实例分析

    - 任何全序上的min和max，例如带有 ≤ 的实数或者整数
    - 某个域的子集合的∩和∪，其中的序是⊆

        **⊆ \subset** **∩ \cap** **∪ \cup**

    - 布尔代数的∧和∨
    - gcd 和 lcm， 序就是∣   注意**NOTE**:在lean4中：∣ 的打法是 **\|** 而不是直接shift+\
    -直接打出|是代表绝对值，注意区分，用来分段的点也是 **·** 就是 **\.**

    -- 向量空间的线性子空间的集合，其中最大下界由交集给出，最小上界由两个空间的和给出，序是包含关系

    -- 一个集合上的拓扑的集合，其中两个拓扑的最大下界由它们的并集生成的拓扑给出，最小上界是它们的交集，排序是逆包含关系


## lean中 `PseudoMetricSpace` 的定义
class PseudoMetricSpace (X : Type u) extends UniformSpace X, HasDist X :=

(dist_self : ∀ x, dist x x = 0)

(dist_comm : ∀ x y, dist x y = dist y x)

(dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

### 🌿 格/序理论公式（来自 `Lattice` 和 `DistribLattice`）

| 中文名称       | Lean 名称/函数            | 用法 | Lean 中定义或说明 |
|----------------|----------------------------|------|------------------|
| 交换律（∧）    | `inf_comm`                 | `x ⊓ y = y ⊓ x` | `inf_comm : x ⊓ y = y ⊓ x` |
| 结合律（∧）    | `inf_assoc`                | `x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z` | `inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z)` |
| 结合律（∨）    | `sup_assoc`                | 同上（∨） | `sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z)` |
| 交换律（∨）    | `sup_comm`                 | `x ⊔ y = y ⊔ x` | `sup_comm : x ⊔ y = y ⊔ x` |
| 吸收律（∨）    | `absorb2` (自定义)         | `x ⊔ x ⊓ y = x` | 通过 `sup_le`, `inf_le_left`, `le_sup_left` 证明 |
| 吸收律（∧）    | `absorb1` (自定义)         | `x ⊓ (x ⊔ y) = x` | 通过 `le_inf`, `inf_le_left`, `le_sup_left` 证明 |
| 分配律1        | `inf_sup_left`             | `x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z` | 定义于 `DistribLattice` |
| 分配律2        | `sup_inf_left`             | `x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)` | 同上 |
| 分配律3        | `inf_sup_right`            | `(x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z` | 同上 |
| 分配律4        | `sup_inf_right`            | `x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z)` | 同上 |
| 定理组合       | `le_antisymm`, `le_inf`, `inf_le_left`, `inf_le_right` | 用于证明等式 | 这些是偏序结构的基本规则组合 |

---

### 🧮 有序环和不等式推导

| 中文名称       | Lean 名称/函数              | 用法 | Lean 中定义或说明 |
|----------------|------------------------------|------|------------------|
| 加法右不等式   | `add_le_add_right`           | `a ≤ b → a + c ≤ b + c` | 定义于 `OrderedAddCommMonoid` |
| 加法左不等式   | `add_le_add_left`            | `a ≤ b → c + a ≤ c + b` | 同上 |
| 乘法保持不等式 | `mul_nonneg`                 | `0 ≤ a ∧ 0 ≤ b → 0 ≤ a * b` | 用于证明非负乘积 |
| 减法转加法     | `sub_eq_add_neg`             | `a - b = a + (-b)` | 用于转换减法为加法 |
| 乘法分配律（减）| `sub_mul`                   | `(a - b) * c = a * c - b * c` | 分配律变形形式 |
| 零加法恒等      | `add_zero`, `zero_add`       | `a + 0 = a` | 加法恒等律 |
| 减法抵消        | `sub_self`, `sub_add_cancel` | `a - a = 0`, `a - b + b = a` | 常用用于反推 |
| 自定义定理      | `aux1`, `aux2`               | `a ≤ b ↔ 0 ≤ b - a` | 结合上面公式构造得出 |

---

### 📏 度量空间中距离公式

| 中文名称       | Lean 名称             | 用法 | Lean 中定义或说明 |
|----------------|------------------------|------|------------------|
| 距离对称性     | `dist_comm`            | `dist x y = dist y x` | 在 `MetricSpace` 中定义 |
| 三角不等式     | `dist_triangle`        | `dist x z ≤ dist x y + dist y z` | 核心不等式，三点路径 |
| 自身距离为 0   | `dist_self x = 0`      | `dist x x = 0` | 定义于度量空间基本属性 |
| 两倍乘法       | `mul_two (a)`          | `2 * a` | 简写表达 |
| 线性推理       | `linarith`             | 自动处理线性不等式 | tactic，自动推理 |

--apply和exact的区别是apply是给定证据，而exact是给定表达式，然后证明其等于这个表达式

`exactly！`

--sq_nonneg是非负平方,pow_two_nonneg是非负的2的幂,应该没什么区别


把里面用到的公式定理的lean名称，用法还有和其在lean中的定义整理markdown给我，我要markdown源代码

### 📌 常见不等式推理定理

| 中文名称             | Lean 名称                        | 用法说明 |
|----------------------|----------------------------------|----------|
| 自反性               | `le_refl`                        | `a ≤ a` 恒成立 |
| 传递性（≤）          | `le_trans`                       | `a ≤ b`, `b ≤ c` 推出 `a ≤ c` |
| 推理小于             | `lt_of_le_of_lt`                 | `a ≤ b`, `b < c` 推出 `a < c` |
| 推理小于（反向）     | `lt_of_lt_of_le`                 | `a < b`, `b ≤ c` 推出 `a < c` |
| 严格小于传递         | `lt_trans`                       | `a < b`, `b < c` 推出 `a < c` |

---

### 📌 指数、对数函数的单调性

| 中文名称             | Lean 名称                        | 用法说明 |
|----------------------|----------------------------------|----------|
| `exp` 单调递增       | `exp_le_exp : exp a ≤ exp b ↔ a ≤ b` | 可用 `.mpr` 回推 `a ≤ b → exp a ≤ exp b` |
| `exp` 严格递增       | `exp_lt_exp : exp a < exp b ↔ a < b` |
| `log` 单调递增       | `log_le_log : 0 < a → a ≤ b → log a ≤ log b` | 思考，已知log a ≤ log b，能推出什么|
| `log` 严格递增       | `log_lt_log : 0 < a → a < b → log a < log b` |

---

### 📌 加法不等式规则

| 中文名称                         | Lean 名称                        | 用法说明 |
|----------------------------------|----------------------------------|----------|
| 分别加法推理（非严格）          | `add_le_add`                     | `a ≤ b`, `c ≤ d` 推出 `a + c ≤ b + d` |
| 左加项                          | `add_le_add_left`               | `a ≤ b → ∀ c, c + a ≤ c + b` |
| 右加项                          | `add_le_add_right`              | `a ≤ b → ∀ c, a + c ≤ b + c` |
| 一个小于一个不等                | `add_lt_add_of_le_of_lt`        | `a ≤ b`, `c < d` 推出 `a + c < b + d` |
| 一个不等一个小于                | `add_lt_add_of_lt_of_le`        | `a < b`, `c ≤ d` 推出 `a + c < b + d` |
| 严格左加项                      | `add_lt_add_left`               | `a < b → ∀ c, c + a < c + b` |
| 严格右加项                      | `add_lt_add_right`              | `a < b → ∀ c, a + c < b + c` |

---

### 📌 正数与非负性

| 中文名称             | Lean 名称                        | 用法说明 |
|----------------------|----------------------------------|----------|
| 加法非负             | `add_nonneg`                     | `0 ≤ a`, `0 ≤ b` 推出 `0 ≤ a + b` |
| 加法正数             | `add_pos`                        | `0 < a`, `0 < b` 推出 `0 < a + b` |
| 一正一非负仍正数     | `add_pos_of_pos_of_nonneg`       | `0 < a`, `0 ≤ b` 推出 `0 < a + b` |
| 指数函数恒正         | `exp_pos`                        | `0 < exp a` |

---

### 📌 平方非负性与相关恒等式

| 中文名称             | Lean 名称                        | 用法说明 |
|----------------------|----------------------------------|----------|
| 平方非负             | `sq_nonneg a`                    | `0 ≤ a^2` |
| 任意幂非负           | `pow_two_nonneg`                 | `0 ≤ a^2`, 更一般形式 |
| 完全平方展开         | `ring`                           | 用于 `(a - b)^2 = ...` 化简计算 |
| 减法与加法转换       | `sub_eq_add_neg`, `sub_add_cancel` | 等价转换 |
| 零加项               | `add_zero`, `zero_add`           | 恒等变换 |

---

### 📌 绝对值相关技巧

| 中文名称             | Lean 名称                        | 用法说明 |
|----------------------|----------------------------------|----------|
| 绝对值界限（双边）  | `abs_le' : |x| ≤ a ↔ -a ≤ x ∧ x ≤ a` | 常用于绝对值换不等式 |
| `.mpr` 用法          | `abs_le'.mpr`                    | 从 `|x| ≤ a` 推出双边不等式 |

---

# C03_Logic

思考这种结构

`p \to q \to r`：如果已知r，能有什么作用？

用apply这个结构，直接把有r的问题转换成p和q的问题。

思考：如果有多种方式可以推导得到r，那么采用不同的方式会有什么区别。

如果已知p和r呢

在这个lamabda演算法结构应该怎么去思考？

example : x ∣ x ^ 2 := by
  apply dvd_mul_of_dvd_left
  norm_num

  /-
  `norm_num`有大用

  1.简化并计算数字表达式：加减乘除，幂，阶乘等

  2.验证基本不等式

  3.处理乘幂组合表达式
  
  4.辅助其他tactic


PseudoMetricSpace 是 Lean 中比 MetricSpace 更宽泛的结构，具有距离函数和常规性质，但不要求不同点之间距离非零。

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb

--证明单调性，要引入两个参数，和这两个参数的关系

  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb


example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

  对比这两种写法，思考一下lamabda演算法的term mode和tactic模式

形如这种形式

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  intro x y ε epos ele1 xlt ylt


如果你想要证明这个结论，你需要先把条件intro出来，然后逐步证明。这便是你为什么要用intro。 **NOTE**: 不过要引用条件，还需要把所有隐含参数也引用出来。

1. 乘积的绝对值等于绝对值的乘积，用的是abs_mul

2. 这种常见的不等式链条一定好好积累。

lt_of_lt_of_le : a < b → b ≤ c → a < c

lt_trans        : a < b → b < c → a < c


```python
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc |x * y| = |x| * |y| := by apply abs_mul
    _ ≤  |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg
    _ < 1 * ε := by apply mul_lt_mul; apply lt_of_lt_of_le xlt ele1; linarith; linarith; linarith;
    _ = ε := by rw [one_mul]
```

这种代码的操作，一定要找清楚逻辑，用apply一步一步去拆解，要把相应的apply的函数给记下来，这样不看goal去拆解才能高效地理解lean4的工作流程。

## 看懂 Crtl+Click 的方法！如何解读子定义文件。



### 🧮 实数基本不等式与绝对值

| 中文名         | Lean 名称       | 用法说明 |
|----------------|------------------|----------|
| 乘积绝对值     | `abs_mul`        | `(x * y)abs = (x)abs * (y)abs` |
| 绝对值非负     | `abs_nonneg`     | `(x)abs ≥ 0` |
| 比较乘积       | `mul_le_mul`     | 若满足 `a ≤ b`, `c ≤ d`, `0 ≤ c`, `0 ≤ d`，则 `a * c ≤ b * d` |
| 小于右乘       | `mul_lt_mul_right` | `0 < c → a < b ↔ a * c < b * c` |
| 恒等恒等       | `rfl`            | 恒等等式 |

---

### 📐 实值函数上下界

| 中文定义             | Lean 表达式                             | 说明 |
|----------------------|------------------------------------------|------|
| 上界谓词定义         | `FnUb f a := ∀ x, f x ≤ a`               | 定义函数在所有 `x` 上有上界 |
| 下界谓词定义         | `FnLb f a := ∀ x, a ≤ f x`               | 同上，定义下界 |
| 上界与加法结合       | `add_le_add`                             | 分别上下界可推出和的上下界 |
| 上界与乘法结合       | `mul_le_mul`（配合非负性）               | 与乘法保持方向一致性 |
| 下界乘法非负性       | `mul_nonneg`                             | 两非负函数的积非负 |

---

### 📈 单调性相关

| 中文定义       | Lean 名称/表达式                     | 说明 |
|----------------|--------------------------------------|------|
| 单调函数定义   | `Monotone f := ∀ x y, x ≤ y → f x ≤ f y` | 可用于组合、数乘 |
| 单调函数复合   | `Monotone (f ∘ g)`                   | 若 `f`, `g` 单调则复合也单调 |
| 数乘保持单调   | `mul_le_mul_of_nonneg_left`          | `0 ≤ c → f x ≤ f y → c * f x ≤ c * f y` |

---

### 🌀 奇偶函数定义与计算

| 中文名       | Lean 定义                    | 用法说明 |
|--------------|-------------------------------|----------|
| 偶函数定义   | `FnEven f := ∀ x, f x = f (-x)` | |
| 奇函数定义   | `FnOdd f := ∀ x, f x = -f (-x)` | |
| 奇 × 奇 → 偶 | `(f x) * (g x)`                | 结合 `neg_mul_neg` |
| 偶 × 奇 → 奇 | `f x * g x` 结合 `neg_mul_eq_mul_neg` |
| 偶 ∘ 奇 → 偶 | `f (g x)`                      | 利用 `g (-x) = -g x` 和 `f (-a) = f a` |

---

### 🔗 集合包含与偏序上界

| 中文名         | Lean 名称                 | 用法说明 |
|----------------|---------------------------|----------|
| 集合包含传递   | `Subset.trans`            | `r ⊆ s`, `s ⊆ t` → `r ⊆ t` |
| 上界定义       | `SetUb s a := ∀ x ∈ s, x ≤ a` | 集合中所有元素都小于等于某数 |
| 上界转移性     | `le_trans (h x xs) h'`    | 继承上界条件向更大上界推广 |

---

### 🎯 函数注入性（Injective）

| 中文名           | Lean 中公式                 | 用法说明 |
|------------------|-----------------------------|----------|
| 数乘函数单射     | `Injective (λ x ↦ c * x)`   | 当 `c ≠ 0` 时成立，使用 `mul_right_inj'` |
| 函数复合单射     | `Injective (g ∘ f)`         | `Injective g` 与 `Injective f` 均成立时 |

---

### 🛠 tactic 技巧汇总

| tactic 名称      | 作用 |
|------------------|------|
| `intro`          | 引入假设、参数 |
| `apply`          | 应用定理、引理、函数 |
| `calc`           | 分步推理链式不等式/等式 |
| `rw`             | 重写等式或已知关系 |
| `dsimp`          | 对定义进行简化（定义层面） |
| `fun x ↦ ...`    | 匿名函数（lambda 表达式） |
| `rfl`            | 恒等 |
| `mp`, `.mp`      | 从双射语句中提取前向推理（如 `↔`） |




