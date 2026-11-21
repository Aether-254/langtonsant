# 交给 Codex 的任务（由 Claude 拟定，用户授权）

先读 `drafts/proof-status.md`、`research/claude-review.md`、`research/claude-codex-sync.md`（文件占用表与协作记录）。

两个任务彼此不冲突，可以开两个会话并行，也可以按顺序在一个会话里做。

## 通用约束

- 不得修改 Claude 占用的文件：`FreshPhases.lean`、`RotatedRecovery.lean`、`FreshPhaseRecovery.lean`、`HardPhaseRecovery.lean`、`scripts/FreshPhaseChecks.lean`、`scripts/ExploreFreshPhaseRecovery.lean`、`research/claude-review.md`。确需修改时，在同步文件中写明理由。
- 不使用 `sorry`、`admit`、`native_decide` 或自定义 `axiom`。有限模拟不能当作无限时间的证明。内核计算统一使用 `decide +kernel`。工具链位于 `tools\lean-4.36.0-windows\bin`。
- 每完成一个里程碑，就在 `research/claude-codex-sync.md` 末尾**追加**进度，写明结论、精确的定理陈述、构建命令和耗时，并更新占用表中自己的那一行。只追加，不改写别人的条目。

## 任务 A：接入构建，完成 L1 与 L3

1. **接入构建。** 需要接入的模块：
   - `FreshObstacleReduction`；
   - `BoundedMemory`（若已能编译）；
   - Claude 已完成的 `FreshPhases`、`RotatedRecovery`、`FreshPhaseRecovery`、`HardPhaseRecovery`，依赖链见同步文件。

   具体工作：
   - 修改 `lakefile.toml`。
   - 在 `scripts/ProofAudit.lean` 中加入以下定理：
     - `highwayConjecture_iff_addBlackStability`
     - `highwayConjecture_iff_freshObstacleStability`
     - `fresh_phase_recovers_except_49`
     - `certified_fresh_phase_recovers`
     - `seed_fresh_phase_classification`
     - `RotatedRecoveryCertificate.after_blocks`
     - `checkShiftedRecovery_sound`
   - 在 `drafts/proof-status.md` 中登记这些结果，沿用原有风格：正式中文，写出精确陈述和边界，不夸大。

   `FreshPhaseRecovery` 的内核检查约需 600 秒，`HardPhaseRecovery` 约需 295 秒。是否放进默认目标由你决定；若不放进默认目标，请单设一个目标并说明。实际运行 `lake build` 和 `ProofAudit` 之后，记录真实结果。

2. **完成 L1。** `BoundedMemory.lean` 已证到 `memoryKey_future`。还缺：
   - 窗口取值的有限性；
   - 由抽屉原理得到重复；
   - 转成固定漂移的 `HighwayFrom`；
   - 用 `escapes_finite_set_after` 排除零漂移。

   陈述按 `research/claude-review.md` 第 3.1.2 节的强定义版本，不需要有限支撑。

3. **`Ballistic.lean`。**
   - L3：有限支撑加 `Ballistic` 推出有界记忆。需写明 `q > 0`、`C ≥ 0`、`T'' ≥ T`，并处理空集的情形。
   - 分解定理：`HC ⇔ (∀ 有限 s, Ballistic s) ∧ PeriodicIsStandard`。正向直接由 `HighwayFrom` 推出弹道性，例如取 `p = 4`、`q = 104`、`C = 108`。

## 任务 B：相位 49 的遗迹回溯（新建 `TrailRetrace.lean`）

只允许新建或修改 `TrailRetrace.lean` 和 `scripts/ExploreTrailRetrace.lean`，以及向同步文件追加内容。若任务 A 同时在进行，不要运行 `lake build`，也不要修改 `lakefile.toml`：编译用 `lean -o`，`LEAN_PATH` 包含 `.lake\build\lib\lean`，中间产生的 olean 放在 `scratch-codex\` 目录下。

**背景。** 标准种子公路（周期 104，漂移 `(-2,-2)`）共有 22 个首访相位，其中 21 个已证明：在 `H` 个周期的历史之后对脚下格翻色，在任意历史下都能恢复（`fresh_phase_recovers_except_49`）。例外是相位 49。探索结果如下：

- 取 `flipTime = 104*H + 49`，对 `H ∈ [11,25]` 都测试过；
- 恢复入口总是绝对坐标 `(39,-37)`，朝南；
- 延迟恰为 `52213 + 104*(H-11)`；
- 最大权重为 7。

由此推断，蚂蚁沿整条公路遗迹走回了种子的原始区域。以上仅是有限观察。

**目标。**

1. **先探索，把结构弄准确。**
   - 翻色后是否存在一段在时间上周期的逆行阶段？推测周期为 104，位移为 `(+2,+2)`。
   - 它从哪里开始、到哪里结束？
   - 到达原始区域时，棋盘是什么状态？这个状态是否与 `H` 无关？
2. **若结构清楚，就在 Lean 中证明。**
   - 仿照 `HighwayCertificate` 的方式（有限检查加对周期数归纳），证明逆行阶段对所有 `H ≥ H0` 成立。
   - 再用一次有限的内核计算收尾“回到原始区域之后”的部分，得到

     ```text
     ∀ k, EventuallyStandard (flipCell (run highwaySeed.toState (104*(k+H0)+49)) ...)
     ```

   - 注意：这个结论只针对 `highwaySeed` 的具体历史。请写明它能否推广到 `AgreesBelow 0` 之外的任意历史；推测不能，因为路径回到了权重 7 > 0 的区域。
3. **若证不出来，** 把确切的障碍写进同步文件，不要含糊带过。

## 任务 C：周期尾部的白背景自洽归约（新建 `PeriodicWord.lean`）

**背景。** 分解定理 `highwayConjecture_iff_ballistic_and_periodicIsStandard`（见 `Ballistic.lean`）把原猜想拆成两半。本任务处理其中的 `PeriodicIsStandard`，目标是把它归约为一个纯组合条件。

Claude 的探索程序 `scripts/periodic_words.c`（只作探索，不进入证明）枚举了满足下述条件的转向字：对 `P = 1..30` 一个都没有；标准公路的 104 位字能通过检查，漂移为 `(-2,-2)`。

**要证明的结论。**

1. **定义白背景自洽字。**
   - 转向字为 `w : Nat → Bool`，只用到 `i < P`。约定 `true` 表示读到黑色、左转。
   - 路径从原点、朝北出发，按 `w` 逐步转向和前进。
   - `ConsistentWord P w` 成立，当且仅当下列条件同时满足：
     - 走完一个周期后朝向回到北；
     - 一个周期的漂移 `v ≠ (0,0)`；
     - 对每个 `i < P`，`w i` 等于第 `i` 步所在格子在双向无限周期路径上更早被访问次数的奇偶。双向无限周期路径定义为 `pos(kP+j) = pos(j) + k·v`，其中 `k` 取全体整数。

   实现时，“更早访问”可以有界地数：满足 `j < i` 且 `pos j = pos i` 的 `j`，加上满足 `pos j = pos i + t·v`、`t ≥ 1` 的 `(j, t)`。因为 `v ≠ 0` 且一个周期内的跨度不超过 `P`，`t` 有显式上界。请给出一个可判定的检查函数，并证明它与命题版本等价。参考实现见 `scripts/periodic_words.c` 中的 `consistent`。

2. **主归约定理（关键部分）。**

   ```text
   theorem periodic_tail_consistent {s : State} {T P : Nat} {v : Point}
       (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
       exists U, T <= U ∧ ConsistentWord P (fun i => readColor s (U + i))
   ```

   直观的证明思路：
   - 由无界性得 `v ≠ 0`，可用 `escapes_finite_set_after`。
   - 有限支撑加上远离初始黑格：足够晚之后，读到的颜色等于该格此前被访问次数的奇偶。
   - 运动周期性：此前的访问都落在周期尾部，并与双向无限周期路径的计数一致，因为访问的时间间隔有界。
   - 旋转、平移不变性：实际朝向不一定是北，用 `Symmetry.lean` 归一化。

   陈述中的量词、旋转归一化方式可以按你的判断调整，但请在同步文件里写明最终的精确陈述。

3. **小周期的内核结论（可选，视内存而定）。**

   ```text
   theorem no_consistent_word_small (P : Nat) (h1 : 0 < P) (h2 : P <= P0) (w : Nat -> Bool) :
       ¬ ConsistentWord P w
   ```

   用 `decide +kernel` 对有限的 `P0` 枚举。并由此推出推论：任何有限支撑状态都不会最终以周期 `P ≤ P0` 运动。`P0` 取内存允许的最大值即可，比如 12 到 16，请实测后决定。

**约束。**

- 只新建或修改 `PeriodicWord.lean`（需要时可拆成多个 `PeriodicWord*.lean`）、`scripts/PeriodicWordChecks.lean`，并在 `lakefile.toml` 默认目标里加上新模块。不要修改其他已有的 Lean 文件。
- **内存警告**：这台机器上一次大的 `decide +kernel` 很容易用掉 2 GB 以上，内存曾多次耗尽并拖垮整台机器。重的检查请拆成多个小模块、逐个编译。不要用 `lake build` 去构建 `SingleBlackEarly` 或 `SingleBlackFull`。
- 不使用 `sorry`、`admit`、`native_decide` 或自定义 `axiom`。有限模拟不能当作无限时间的证明。
- 每完成一个里程碑，就在 `research/claude-codex-sync.md` 末尾追加：精确陈述、构建命令、耗时、公理审计结果。只追加，不改写别人的条目。
