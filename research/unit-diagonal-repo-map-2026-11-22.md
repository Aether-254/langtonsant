# 单位对角漂移排除形式化：仓库全景映射与接口设计

日期：2026-11-22。工作分支：`single-black-cell`（仓库根目录：`D:\langtonsant`）。工具链：`leanprover/lean4:v4.36.0`（无 Mathlib，仅依赖标准库 `Std` 与 `Lean.Elab.Tactic.Omega`）。

本文面向在**纯 Lean 内核**（不使用 `sorry`、自定义 `axiom` 或 `native_decide`）中形式化 Hao Ke 的单位对角漂移排除定理：任何从有限初始黑格集出发、最终周期运行的经典 Langton 蚂蚁轨道，其单周期**完整位移（full displacement）**不可能为 `(1, -1)` 及其四分之一转旋转 `{(1, -1), (-1, -1), (-1, 1), (1, 1)}`（不设周期、宽度、增长或种子规模上界，亦不要求周期最小）。数学背景摘要见 [drift-ke-source-audit-2026-11-22.md](file:///D:/langtonsant/research/drift-ke-source-audit-2026-11-22.md#L7-L25)。

---

## 1. 现有 Lean 基础设施盘点

全仓库根目录下所有 `.lean` 源文件均已核查：**零 `sorry`、零自定义 `axiom`、零 `native_decide`**。`LangtonsAnt` 与 `PeriodicWords` 两个默认库全部属于**纯内核证明**（公理依赖仅限于标准三公理 `propext`、`Classical.choice`、`Quot.sound` 的子集）。全仓库唯一引入 `native_decide`（信任基础包含 Lean 编译器与原生代码运行库）的库是 `PeriodicNative`（及预编译辅助库 `PeriodicFastLib` 在 `PeriodicNative` 中的调用）。

### 1.1 基础模型、动力学、有限支撑与对称性（`LangtonsAnt` 库，纯内核）

| 文件路径 | 核心声明 | 语义与作用 | 信任边界 |
| :--- | :--- | :--- | :--- |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean) | `Point := Int × Int`, `Board := Point -> Bool`, `Direction` (`north \| east \| south \| west`) | 无限二维整数格网；**`false` = 白格（右转 R），`true` = 黑格（左转 L）**；`Direction` 派生 `DecidableEq, Repr` | 纯内核 |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean#L21-L60) | `Direction.right`, `Direction.left`, `Direction.horizontal`, `turn`, `move`, `flip`, `State`, `step`, `run` | `turn black d := if black then d.left else d.right`；`move` 采用标准笛卡尔坐标（北 `+y`、东 `+x`、南 `-y`、西 `-x`）；`step` 先按当前格颜色转向 `d`，翻转当前格，再沿 `d` 移动一步并令新朝向为 `d`；`run s n` 为 `n` 步迭代 | 纯内核 |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean#L62-L99) | `run_zero`, `run_succ`, `run_add`, `flip_same`, `flip_other`, `flip_twice`, `FiniteSupport`, `finiteSupport_flip`, `finiteSupport_run` | `FiniteSupport board := ∃ cells : List Point, ∀ p, board p = true → p ∈ cells`；有限支撑在任意有限步运行下保持 | 纯内核 |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean#L101-L135) | `weight`, `axisParity`, `axisParity_step`, `axisParity_run`, `same_cell_same_axis`, `corner_color` | **`weight p := p.1 + p.2`**（恰好是位移 `(1, -1)` 下的不变横向层坐标！）；`axisParity` 守恒推出同一物理格的所有到达朝向必具有相同横纵轴（`same_cell_same_axis`） | 纯内核 |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean#L137-L244) | `Recurrent`, `recurrent_tail`, `finite_range_recurrent_max`, `recurrent_not_fixed_color`, `escapes_finite_set`, `escapes_finite_set_after` | 无界逃逸定理（任意棋盘、无需有限支撑） | 纯内核 |
| [LangtonsAnt.lean](file:///D:/langtonsant/LangtonsAnt.lean#L246-L286) | `HighwayFrom`, `DiagonalDrift`, `Period104Conjecture`, `blank`, `readColor`, `standardColor`, `StandardHighwayFrom`, `HighwayConjecture`, `highwayConjecture_implies_period104` | `HighwayFrom s T P v` 定义从时刻 `T` 起每 `P` 步位置平移 `v` 且朝向复原；`readColor s n := (run s n).board (run s n).pos`；`DiagonalDrift v` 专指 `(±2, ±2)` | 纯内核 |
| [FiniteAnt.lean](file:///D:/langtonsant/FiniteAnt.lean) | `FiniteState`, `FiniteState.toState`, `FiniteState.step`, `FiniteState.run`, `FiniteState.toState_run`, `FiniteState.finiteSupport` | 有限黑格列表实现及其与 `State` 模型的等价性 | 纯内核 |
| [Highway.lean](file:///D:/langtonsant/Highway.lean#L5-L76) | `addPoint`, `subPoint`, `weight_addPoint`, `subPoint_addPoint`, `addPoint_subPoint`, `translate`, `translate_run`, `translate_readColor`, `move_addPoint` | 点加减法、平移等变性、`weight_addPoint` 及半平面证书 `AgreesBelow` / `HighwayCertificate` | 纯内核 |
| [Symmetry.lean](file:///D:/langtonsant/Symmetry.lean) | `rotatePoint`, `rotateDir`, `inverseRotation`, `negPoint`, `rotateState`, `rotate_run`, `rotate_readColor`, `HighwayFrom.rotate`, `HighwayFrom.translate`, `finiteSupport_rotate`, `finiteSupport_translate`, `pose`, `normalize`, `pose_normalize`, `normalize_pose`, `normalize_run`, `normalize_readColor`, `finiteSupport_normalize` | 四方向旋转与刚体归一化；`rotatePoint r` 以北向像为参数（`.east` 为顺时针 90°）；`rotateState` 与 `normalize` 均保持 `readColor` 与 `FiniteSupport` | 纯内核 |
| [DelayedHighway.lean](file:///D:/langtonsant/DelayedHighway.lean#L5-L85) | `turn_color_injective`, `HighwayFrom.reads_periodic`, `exists_first_nat`, `board_unchanged_of_avoids` | `HighwayFrom` 蕴含尾段读色 `P` 周期（`reads_periodic`）；无 Mathlib 下的最小自然数提取引理 `exists_first_nat`；未访问格保色引理 `board_unchanged_of_avoids` | 纯内核 |
| [FreshPhases.lean](file:///D:/langtonsant/FreshPhases.lean#L15-L18) | `FirstVisitAt` | `FirstVisitAt s n := ∀ j < n, (run s j).pos ≠ (run s n).pos`（物理轨道首次访问定义，其余内容针对标准 104 步种子） | 纯内核 |
| [BoundedMemory.lean](file:///D:/langtonsant/BoundedMemory.lean) | `BoundedMemoryFrom`, `EventuallyBoundedMemory`, `finite_list_repeats`, `HighwayFrom.drift_ne_zero`, `BoundedMemoryFrom.highway`, `EventuallyBoundedMemory.highway` | `HighwayFrom.drift_ne_zero` 证明任意正周期公路必有 `v ≠ (0, 0)`；`finite_list_repeats` 为无 Mathlib 的列表鸽巢原理 | 纯内核 |
| [Ballistic.lean](file:///D:/langtonsant/Ballistic.lean) | `linearForm`, `BallisticFrom`, `Ballistic`, `Ballistic.boundedMemory`, `Ballistic.highway`, `PeriodicIsStandard`, `highwayConjecture_iff_ballistic_and_periodicIsStandard` | `linearForm a b x := a * x.1 + b * x.2`；`PeriodicIsStandard`（一切有限支撑周期尾均为标准公路）及主猜想分解 | 纯内核 |

### 1.2 周期字、双向周期轨道、有限实现与分类归约（`PeriodicWords` 库，纯内核）

| 文件路径 | 核心声明 | 语义与作用 | 信任边界 |
| :--- | :--- | :--- | :--- |
| [PeriodicWordCore.lean](file:///D:/langtonsant/PeriodicWordCore.lean) | `wordTrace`, `wordPos`, `wordDrift`, `scalePoint`, `priorShift`, `EarlierPhase`, `checkEarlierPhase`, `priorPhases`, `ConsistentWord`, `checkConsistentWord`, `checkConsistentWord_iff`, `mem_priorPhases`, `priorPhases_nodup`, `wordPos_bounds`, `period_overlap_bound`, `wordTrace_axis`, `ConsistentWord.even`, `no_consistent_word_odd`, **`biPeriodicPos`**, `earlierPhase_iff_integer_period`, `biPeriodicPos_injective_period`, **`mem_priorPhases_iff_integer_period`**, `wordTrace_congr`, `priorPhases_congr`, `ConsistentWord.congr` | **核心基础设施**：<br>• `wordTrace w n`：从 `((0, 0), .north)` 出发按转向字 `w : Nat → Bool` 走 `n` 步后的位姿 `(pos, dir)`；`wordDrift P w := wordPos w P`。<br>• `ConsistentWord P w`：`(wordTrace w P).2 = .north ∧ wordDrift P w ≠ (0, 0) ∧ ∀ i < P, w i = decide ((priorPhases P w i).length % 2 = 1)`。<br>• **`biPeriodicPos P w k j := addPoint (wordPos w j) (scalePoint (wordDrift P w) k)`**：双向无限周期路径在周期 `k : Int`、相位 `j < P` 的坐标。<br>• **`mem_priorPhases_iff_integer_period`**：`j ∈ priorPhases P w i ↔ ∃ k : Int, k * P + j < i ∧ biPeriodicPos P w k j = wordPos w i`——这正是连接 `priorPhases` 与稳定访问时间 $\tau_i$ 的关键桥梁。<br>• `wordTrace_axis`：`(wordTrace w n).2.horizontal = decide (n % 2 = 1)`；`ConsistentWord.even`：`P % 2 = 0`。 | 纯内核 |
| [PeriodicWord.lean](file:///D:/langtonsant/PeriodicWord.lean) | `wordTrace_reads`, `wordPos_reads`, `HighwayFrom.word_blocks`, `HighwayFrom.word_position`, `earlierVisits`, `mem_earlierVisits`, `earlierVisits_nodup`, `board_visit_parity`, `HighwayFrom.phase_injective`, `HighwayFrom.exists_white_copy`, `HighwayFrom.word_drift`, `HighwayFrom.visits_phase_iff`, `HighwayFrom.visits_phase_perm`, `periodic_word_consistent_at_origin`, **`periodic_tail_consistent_at_start`**, `periodic_tail_consistent`, `no_odd_periodic_tail`, `standard_word_consistent` | 证明任意有限支撑轨道的周期尾 `HighwayFrom s T P v`（`0 < P`）在起点 `T` 归一化后即满足 `ConsistentWord P (fun i => readColor s (T + i))`，且对足够晚的周期 `K ≥ 2*P`，实际访问列表 `earlierVisits` 模 `P` 的像恰为 `priorPhases` 的排列（`visits_phase_perm`）。 | 纯内核 |
| [PeriodicWordRealizationTrace.lean](file:///D:/langtonsant/PeriodicWordRealizationTrace.lean) | `repeatWord`, `repeatWord_prefix`, `repeatWord_trace`, `repeatWord_drift`, `repeatWord_trace_period`, `repeatWord_pos_blocks`, `repeatWord_position`, `repeatWord_phase_injective`, `wordEarlierVisits`, `mem_wordEarlierVisits`, `repeatWord_visits_phase_iff`, `repeatWord_visits_phase_perm` | 将有限前缀 `w` 周期延拓为 `repeatWord P w n := w (n % P)`，证明其位置块分解、相位单射性以及 `wordEarlierVisits` 与 `priorPhases` 的排列对应。 | 纯内核 |
| [PeriodicWordRealization.lean](file:///D:/langtonsant/PeriodicWordRealization.lean) | `prescribedBoard`, `prescribedState`, `prescribedBoard_finite`, `prescribedBoard_parity`, `ConsistentWord.prescribed_read`, `wordRealization`, `wordRealization_finite`, `ConsistentWord.realization_run`, `ConsistentWord.realization_reads`, `ConsistentWord.realization_highway`, `ConsistentWord.realizable`, **`consistentWord_iff_finite_realization`** | 构造性逆向定理：每个 `ConsistentWord P w`（`0 < P`）均可由显式有限支撑初态 `wordRealization P w` 实现，且从时刻 `0` 起满足 `HighwayFrom s 0 P (wordDrift P w)` 与 `readColor s n = w (n % P)`。 | 纯内核 |
| [PeriodicWordReduction.lean](file:///D:/langtonsant/PeriodicWordReduction.lean) | `ConsistentWordsAreStandard`, `finite_word_standard_extends`, `periodicIsStandard_iff_consistentWordsAreStandard`, `highwayConjecture_iff_ballistic_and_consistentWordsAreStandard` | 证明 `PeriodicIsStandard ↔ ConsistentWordsAreStandard`，无过度近似。 | 纯内核 |
| [BallisticGeneral.lean](file:///D:/langtonsant/BallisticGeneral.lean) | `driftNorm`, `driftL1`, `PeriodicTail`, `linearForm_add`, `linearForm_neg_drift`, `linearForm_move_le`, `driftNorm_pos`, `HighwayFrom.ballisticFrom_of_pos`, `ballistic_iff_periodicTail`, `ballistic_iff_eventuallyBoundedMemory`, `highwayConjecture_iff_periodicTail_and_consistentWordsAreStandard` | 任意正周期尾部均为弹道运动；有限支撑下 `Ballistic ↔ PeriodicTail ↔ EventuallyBoundedMemory`。 | 纯内核 |
| [PeriodicWordEnumeration.lean](file:///D:/langtonsant/PeriodicWordEnumeration.lean), `PeriodicWordCheck8..12H.lean`, [PeriodicWordSmall.lean](file:///D:/langtonsant/PeriodicWordSmall.lean) | `checkNoWords`, `checkNoWords_sound`, `no_consistent_word_small`, `no_periodic_tail_small` | 穷举排除所有 `0 < P ≤ 13` 的自洽字与有限支撑周期尾（偶数 2..12 用 `decide +kernel`，奇数用 `no_consistent_word_odd`）。 | 纯内核（含重计算 `decide +kernel` 串行链） |
| [PeriodicBackgroundWord.lean](file:///D:/langtonsant/PeriodicBackgroundWord.lean), [DualFrontCountermodel.lean](file:///D:/langtonsant/DualFrontCountermodel.lean), [AxisClockObstruction.lean](file:///D:/langtonsant/AxisClockObstruction.lean) | `BackgroundWord`, `backgroundRealization`, `PastPeriodRecord`, `cyclicRecordCheck_iff`, `DualFrontCountermodel.highway` / `not_finite` / `not_consistent`, `AxisClockObstruction.no_universal_strict_clock` | 周期不变无限背景的反模型与时钟障碍；说明去掉白背景/有限支撑后结论不成立。 | 纯内核 |

### 1.3 记录前沿、访问计数与首次返回基础设施（`RecordPair` / `RecordSupport`，纯内核）

| 文件路径 | 核心声明 | 语义与作用 | 信任边界 |
| :--- | :--- | :--- | :--- |
| [RecordPair.lean](file:///D:/langtonsant/RecordPair.lean) | `prescribedBoard_fresh`, `prescribedBoard_unvisited`, `prescribedBoard_alternate`, `gain`, `UnitSign`, `linearForm_move_gain`, `gain_unit`, `gain_right_right`, `right_four`, `turn_black_eq`, `horizontal_right`, `gain_unique`, `move_square`, `move_two_ne`, `wordPos_pred`, `wordDir_pred`, `IsRecord`, `record_pair`, `linearForm_wordPos_le`, **`linearForm_wordPos_parity`**, `exists_least`, `FirstReach`, `PairStart`, `ConsistentWord.record_data`, **`ConsistentWord.four_mul_driftL1_le`**, **`ConsistentWord.front_factor`**, `driftL1_rotatePoint`, `periodic_tail_record_data` | **可直接复用的工具丰富**：<br>• `prescribedBoard_fresh` / `prescribedBoard_unvisited` / `prescribedBoard_alternate`：预置棋盘上首次访问读白、区间未访保色、相邻访问翻色。<br>• `linearForm_wordPos_parity`：`(linearForm s1 s2 (wordPos u t) - t) % 2 = 0`（取 `s1 = s2 = 1` 即得 `(weight (wordPos w t) - t) % 2 = 0`）。<br>• `exists_least`：无 Mathlib 的最小元素提取。<br>• **`ConsistentWord.front_factor`**：每个自洽字必含循环因子 `1 0 0 0 0 1`（4 次连续 `false` 右转！立即可推出轨迹遍历全部 4 个朝向，可用于循环移位归一）。<br>• `ConsistentWord.four_mul_driftL1_le`：`4 * driftL1 (wordDrift P w) ≤ P`。<br>• `periodic_tail_record_data`：将 `ConsistentWord` 结论从 `wordDrift` 提升回任意有限支撑轨道的模板代码（见第 635–670 行）。 | 纯内核 |
| [RecordSupport.lean](file:///D:/langtonsant/RecordSupport.lean) | `black_has_white_source`, `RunRecord`, `finiteSupport_white_above`, `run_level_succ`, `record_support_pose`, `record_black_has_support_excursion`, `record_predecessor_max`, `record_base_heading`, `record_base_prior_white`, `white_reads_final_white_no_visit`, **`record_black_has_first_return`**, `same_front_sources_ordered` | 实际轨道上新记录前沿的前导黑读必为初始白格的**第二次访问**（rank = 1），唯一先前访问为同位姿白读，且同前沿支撑区间按时间严格分离。其中 `black_has_white_source` 和 `white_reads_final_white_no_visit` 为通用的轨道访问/翻色引理。 | 纯内核 |
| [RecordSupportExamples.lean](file:///D:/langtonsant/RecordSupportExamples.lean) | `FirstSupportAt`, `firstSupportAt_of_source`, `crossing_distinct_fronts`, `source_link_fails`, `standard_sources` | 反例与正例证书（含 `decide +kernel`）；表明跨前沿区间可交错、一般暂态无来源链接。 | 纯内核 |

### 1.4 仅依赖 `native_decide` 的外部边界（**不可导入**）

| 文件路径 | 核心声明 | 语义与信任边界 |
| :--- | :--- | :--- |
| [PeriodicWordFast.lean](file:///D:/langtonsant/PeriodicWordFast.lean) | `fastCheck`, `fastCheck_eq`, `fastScan`, `fastScan_sound` | 本身是纯内核等价性证明，归属 `PeriodicFastLib`（`precompileModules = true`），供 `PeriodicNative` 调用 |
| [PeriodicNative/Small.lean](file:///D:/langtonsant/PeriodicNative/Small.lean), [PeriodicNative/Small37.lean](file:///D:/langtonsant/PeriodicNative/Small37.lean) | `no_consistent_word_native`, `no_periodic_tail_native`（`P ≤ 33`）, `no_consistent_word_native37`, `no_periodic_tail_native37`（`P ≤ 37`） | **依赖大量 `native_decide` 公理**（Trust base 包含 Lean 编译器、原生运行时及 Kaggle 外部执行环境）。单位对角排除的新模块**绝对不得导入** `PeriodicNative.*` 或 `PeriodicWordFast`。 |

---

## 2. 主定理的仓库词汇表陈述与既有结论衔接

### 2.1 建议定义与主定理精确签名

与 [LangtonsAnt.lean:252](file:///D:/langtonsant/LangtonsAnt.lean#L252) 中的 `DiagonalDrift` 保持完全一致的风格，定义单位对角位移谓词（同时给出与 `UnitSign` 及四分之一转旋转的等价引理）：

```lean
/-- 完整单周期位移为单位对角向量 `(±1, ±1)`，即 `(1, -1)` 及其四分之一转旋转。 -/
def UnitDiagonalDrift (v : Point) : Prop :=
  (v.1 = 1 ∨ v.1 = -1) ∧ (v.2 = 1 ∨ v.2 = -1)

theorem unitDiagonalDrift_iff_rotate (v : Point) :
    UnitDiagonalDrift v ↔ exists r : Direction, v = rotatePoint r (1, -1)

theorem unitDiagonalDrift_rotatePoint (r : Direction) {v : Point}
    (hv : UnitDiagonalDrift v) : UnitDiagonalDrift (rotatePoint r v)
```

围绕这一定义，建议按“规范化字 → 四旋转字 → 有限支撑轨道”三层暴露定理签名：

1. **规范方向自洽字定理（解析证明的核心落点）**：
   ```lean
   /-- 核心解析定理：白背景自洽字不可能具有完整位移 `(1, -1)`。 -/
   theorem ConsistentWord.drift_ne_unitSE {P : Nat} {w : Nat -> Bool}
       (h : ConsistentWord P w) : wordDrift P w ≠ (1, -1)
   ```
   > 注：`0 < P` 可由 `h.2.1 : wordDrift P w ≠ (0, 0)` 直接推出（若 `P = 0` 则 `wordDrift 0 w = (0, 0)`），因此无需额外作为假设；若与 `RecordPair.lean` 风格对齐，也可同时导出带 `(hP : 0 < P)` 或不带的版本。

2. **四旋转自洽字定理**：
   ```lean
   /-- 任意白背景自洽字都不可能具有单位对角完整位移 `(±1, ±1)`。 -/
   theorem ConsistentWord.not_unitDiagonalDrift {P : Nat} {w : Nat -> Bool}
       (h : ConsistentWord P w) : ¬ UnitDiagonalDrift (wordDrift P w)
   ```

3. **有限支撑轨道定理（面向最终用户的头条陈述）**：
   ```lean
   /-- Ke 单位对角排除定理（轨道形式）：从有限初始黑格集出发，任意正周期的最终周期尾
   都不可能具有单位对角完整位移 `(±1, ±1)`。不设周期、宽度、增长或种子大小上界，
   亦不要求 `P` 为最小周期。 -/
   theorem no_unit_diagonal_periodic_tail {s : State} {T P : Nat} {v : Point}
       (hs : FiniteSupport s.board) (hP : 0 < P) (hv : UnitDiagonalDrift v) :
       ¬ HighwayFrom s T P v
   ```
   另可顺手给出去掉 `hP : 0 < P` 的版本（因为 `P = 0` 时 `HighwayFrom s T 0 v` 推出 `v = (0, 0)`，与 `UnitDiagonalDrift v` 矛盾），以及针对 `(1, -1)` 的直接特化：
   ```lean
   theorem no_unit_diagonal_periodic_tail' {s : State} {T P : Nat} {v : Point}
       (hs : FiniteSupport s.board) (hv : UnitDiagonalDrift v) :
       ¬ HighwayFrom s T P v
   ```

### 2.2 与既有头条定理的关系与已有覆盖范围

1. **在主猜想分解中的定位**：
   - [BallisticGeneral.lean:165](file:///D:/langtonsant/BallisticGeneral.lean#L165) 与 [PeriodicWordReduction.lean:85](file:///D:/langtonsant/PeriodicWordReduction.lean#L85) 将开放的 `HighwayConjecture` 等价分解为两个开放块：
     $$\text{HighwayConjecture} \iff (\forall s,\; \text{FiniteSupport } s.\text{board} \to \text{PeriodicTail } s) \;\land\; \text{ConsistentWordsAreStandard}.$$
   - `ConsistentWord.not_unitDiagonalDrift` 是第二个开放块 `ConsistentWordsAreStandard` 的一条**无周期上界、全称成立的必要结构排除定理**：它证明任何满足 `ConsistentWord P w` 的漂移向量都不可能是 `(±1, ±1)`。它**不**解决 `ConsistentWordsAreStandard`（例如标准公路 `(±2, ±2)`、其他对角倍数 `(±m, ±m)` 及非对角/轴向漂移仍开放），更不解决第一开放块 `PeriodicTail`。
2. **既有定理已覆盖的局部交集**：
   - [RecordPair.lean:605](file:///D:/langtonsant/RecordPair.lean#L605) 的 `ConsistentWord.four_mul_driftL1_le` 给出 $4(|v_1|+|v_2|) \le P$；对单位对角漂移仅推出 $P \ge 8$。
   - [PeriodicWordCore.lean:147](file:///D:/langtonsant/PeriodicWordCore.lean#L147) 的 `no_consistent_word_odd` 与 [PeriodicWord.lean:232](file:///D:/langtonsant/PeriodicWord.lean#L232) 的 `no_odd_periodic_tail`（纯内核）排除全部奇数 $P$。
   - [PeriodicWordSmall.lean:7,20](file:///D:/langtonsant/PeriodicWordSmall.lean#L7-L23) 的 `no_consistent_word_small` / `no_periodic_tail_small`（纯内核）排除全部 $0 < P \le 13$（不限漂移）。
   - [PeriodicNative/Small37.lean:9,19](file:///D:/langtonsant/PeriodicNative/Small37.lean#L9-L22) 的 `no_consistent_word_native37` / `no_periodic_tail_native37`（依赖 `native_decide`）排除全部 $0 < P \le 37$（不限漂移）。
   - **真正新增的部分**：在纯内核中对**所有 $P \ge 14$**（乃至与 `native_decide` 相比对所有 $P \ge 38$）全称排除单位对角完整位移 `(±1, ±1)`，且无需任何穷举或外部信任基。
3. **与其他漂移结果的互补**：
   - `ConsistentWord.not_unitDiagonalDrift` 不与 [LangtonsAnt.lean:252](file:///D:/langtonsant/LangtonsAnt.lean#L252) 的 `DiagonalDrift`（`(±2, ±2)`）或 [StandardHighway.lean](file:///D:/langtonsant/StandardHighway.lean) 的 `standard_word_consistent`（`P = 104`, `wordDrift = (-2, -2)`）冲突，因为排除的是完整位移 `(±1, ±1)` 而非本原方向。
   - 后续若形式化生长数下界 $g \ge 8$（参见 `periodic-growth-closure.md`），本定理是排除 $g = 4$ 情形的三支之一。

---

## 3. 缺口分析、建议模块架构与 `lakefile.toml` 影响

### 3.1 仓库尚缺的概念与引理（以及可复用捷径）

以下逐项列出证明 Ke 单位对角排除定理所需、但当前仓库尚未定义的新对象与引理：

1. **单位对角位移谓词与旋转归约（含循环移位引理）**：
   - 缺失：`UnitDiagonalDrift`；**自洽字的循环移位保自洽性引理** `ConsistentWord.cyclicShift`（若 `ConsistentWord P w`，令 `w_a i := w ((a + i) % P)`，则 `ConsistentWord P w_a` 且 `wordDrift P w_a = rotatePoint (inverseRotation (wordTrace w a).2) (wordDrift P w)`）；以及**全朝向可达引理** `ConsistentWord.exists_phase_dir`（对任意 `d : Direction`，存在 `a < P` 使 `(wordTrace w a).2 = d`）。
   - **复用捷径**：
     - `ConsistentWord.exists_phase_dir` 可从 [RecordPair.lean:610](file:///D:/langtonsant/RecordPair.lean#L610) 的 `ConsistentWord.front_factor` 几乎直接推出：因循环字含 4 个连续的 `false`（右转 `R`），朝向依次经历 `d, d.right, d.right.right, d.right.right.right`，覆盖全部 4 个方向。
     - `ConsistentWord.cyclicShift` 可经由 [PeriodicWordRealization.lean:115](file:///D:/langtonsant/PeriodicWordRealization.lean#L115) 的 `ConsistentWord.realizable` 得到 `s := wordRealization P w`，再在时刻 `a` 对 `HighwayFrom s a P (wordDrift P w)` 调用 [PeriodicWord.lean:198](file:///D:/langtonsant/PeriodicWord.lean#L198) 的 `periodic_tail_consistent_at_start` 直接得到，无需重复写 `priorPhases` 的排列证明！
     - 反向地，对于轨道定理 `no_unit_diagonal_periodic_tail`，也可以先用 [Symmetry.lean:104](file:///D:/langtonsant/Symmetry.lean#L104) 的 `HighwayFrom.rotate` 把 `v` 旋至 `(1, -1)`，再利用上述全朝向可达引理找到 `a < P` 使 `(run s' (T + a)).dir = .north`，最后调用 `periodic_tail_consistent_at_start` 归约到 `wordDrift P w' = (1, -1)`。

2. **横向层、纵向提升量与稳定访问时间（针对 `v = (1, -1)`）**：
   - 缺失：
     - 横向层坐标：`layer p := weight p`（复用 [LangtonsAnt.lean:101](file:///D:/langtonsant/LangtonsAnt.lean#L101) 的 `weight`：`x + y` 在加 `(1, -1)` 下不变）。
     - 纵向提升量：`lift p := p.1`（因为任意位于层 `L = x + y` 的格点 `p = (x, y)` 唯一写成 `(0, L) + x • (1, -1)`，单周期平移使 `lift` 恰增 `1`！）。
     - 稳定访问时间：`stableTime P w i : Int := (i : Int) - (P : Int) * (wordPos w i).1`。
     - 层相位集合：`layerPhases P w L : List Nat := (List.range P).filter (fun i => decide (weight (wordPos w i) = L))`。
     - 双向周期访问的唯一表示与 `stableTime` 单射性：对同层相位 `i, j < P`，`biPeriodicPos P w k j = (0, L) ↔ k = -(wordPos w j).1`，其全局双向时间恰为 `stableTime P w j`；且 `stableTime P w i = stableTime P w j → i = j`。

3. **稳定访问秩（重大简化：无需手写排序！）**：
   - 缺失：`stableRank` 的定义与严格保序双射性质。
   - **关键发现（与现有代码零缝隙对接）**：
     在 `wordDrift P w = (1, -1)` 时，将 [PeriodicWordCore.lean:207](file:///D:/langtonsant/PeriodicWordCore.lean#L207) 的 `mem_priorPhases_iff_integer_period` 展开：
     $$j \in \text{priorPhases } P\; w\; i \iff j < P \;\land\; \text{weight}(\text{wordPos } w\; j) = \text{weight}(\text{wordPos } w\; i) \;\land\; \text{stableTime } P\; w\; j < \text{stableTime } P\; w\; i.$$
     因此，**`(priorPhases P w i).length` 本身就已经是相位 `i` 在其平移类（层 `L`）中的 0-基稳定访问秩**！
     - `ConsistentWord P w` 的第三条条件 `w i = decide ((priorPhases P w i).length % 2 = 1)` 直接给出“秩 0 读 `false`（R）、秩 1 读 `true`（L）、按秩严格交替”！
     - 同层内 `stableTime P w j < stableTime P w i → (priorPhases P w j).length < (priorPhases P w i).length` 可由 `priorPhases` 的真子集关系（结合 `Nodup` 长度严格单调引理）直接证明，**完全不需要引入排序算法（如 `mergeSort`）**！
     - 只需补少量 `List.Nodup` 辅助引理（子列表长度不等、真子集严格小于、`rank : layerPhases → Fin m_L` 双射及按秩反查相位 `phaseOfRank`），以及“无中间稳定时间 $\iff$ 稳定秩恰好加一”：
       $$\text{stableRank } j = \text{stableRank } i + 1 \iff \text{stableTime } i < \text{stableTime } j \land \neg \exists k \in \text{layerPhases},\; \text{stableTime } i < \text{stableTime } k < \text{stableTime } j.$$

4. **双向步转移、端口（到达/离开朝向）与首次物理回返秩相邻引理**：
   - 缺失：
     - 双向时间索引 `biTime k i := k * (P : Int) + (i : Int)` 或按 `ℤ` 参数化的路径位置/到达朝向/离开朝向函数（注意：利用 `repeatWord P w` 在充分大周期 `K ≥ 2*P` 的实际窗口中，也可以把所有有限步物理路径拉回 `Nat` 上的 `wordTrace (repeatWord P w)`，从而直接复用 `repeatWord_pos_blocks`、`prescribedBoard_alternate` 等 `Nat` 引理，避免为 `ℤ` 重新写一遍全套归纳引理！建议仔细权衡：在 `biPeriodicPos` 上做一步转移很短，或统一包装一个 `stepZ` / 模 `P` 周期相位转移 `nextPhase i := (i + 1) % P`）。
     - **同向有向格边按稳定时间保序匹配引理**（例如从层 `L` 向层 `L ± 1` 的所有跨层步 `E / N / W / S`，其出发点的稳定时间与到达点的稳定时间相差一个常数——具体地：一步向 `E` 使 `lift` 增 `1`、层增 `1`，稳定时间变化 `1 - P`；一步向 `N` 使 `lift` 不变、层增 `1`，稳定时间变化 `+1`；一步向 `S` 使 `lift` 不变、层减 `1`，稳定时间变化 `+1`；一步向 `W` 使 `lift` 减 `1`、层减 `1`，稳定时间变化 `1 + P`！）。
     - **首次物理回返秩加一引理**：沿连续路径从格 `c` 出发，在首次回到同一物理格 `c` 之前未再次经过 `c`，则起点与回返点必在同层且稳定秩恰好满足 `rank(return) = rank(start) + 1`。这是整个证明最核心的动力学桥接引理（尤其用于排除跨过奇数个中间秩的情形，以及首层两步 `E, S` 路径给出稳定时间差 `2 - P` 的关键推理）。

5. **极值层与向内三层的端口字及交错矛盾**：
   - 缺失：
     - 极值层存在性：`maxLayer`（所有 `weight (wordPos w i)` 的最大值，用 `List.max` 构造，类似 [LangtonsAnt.lean:170](file:///D:/langtonsant/LangtonsAnt.lean#L170) 和 [RecordSupport.lean:35](file:///D:/langtonsant/RecordSupport.lean#L35)）。
     - 极值层 `L_max` 恰有 1 次访问（秩 0，读 `false` = R，入向与出向唯一锁定，例如东入南出或北入东出——须按当前坐标与顺时针转向核对精确方向！）。
     - 向内第 1 层（`L_max - 1`）、第 2 层（`L_max - 2`）的端口字与出入数量推导，以及第 3 层（`L_max - 3`）中偶数秩与奇数秩归属两张列表（`p_2 = q_1 + 1`, `p_4 = q_3 + 1`, `p_1 ≠ q_1`, `p_4 ≠ q_4`）的纯组合矛盾引理。

### 3.2 建议的模块落位与 `lakefile.toml` / 导入链影响

- **建议主文件**：`D:\langtonsant\UnitDiagonalObstruction.lean`（若后续篇幅超过约 600–800 行，可拆为 `UnitDiagonalRank.lean`（稳定时间、稳定秩、跨层边与首次回返）+ `UnitDiagonalObstruction.lean`（极值层至三层交错矛盾与主定理））。
- **建议验证/公理审计脚本**：`D:\langtonsant\scripts\UnitDiagonalChecks.lean`（仿照 [scripts/BrainstormChecks.lean](file:///D:/langtonsant/scripts/BrainstormChecks.lean)，对核心定理执行 `#print axioms` 与签名冒烟测试）。
- **导入选择（关键！）**：
  - `UnitDiagonalObstruction.lean` 应 **`import RecordPair`**（单行导入即可传递引入 `LangtonsAnt`, `Highway`, `Symmetry`, `DelayedHighway`, `BoundedMemory`, `Ballistic`, `PeriodicWordCore`, `PeriodicWord`, `PeriodicWordRealizationTrace`, `PeriodicWordRealization`, `PeriodicWordReduction`, `BallisticGeneral`, `RecordPair` 全部基础模块，包括 `ConsistentWord.front_factor` 与 `linearForm_wordPos_parity`）。
  - **切勿导入 `PeriodicWordSmall`、`PeriodicWordCheck*`、`PeriodicWordFast` 或 `PeriodicNative.*`**：
    - `PeriodicWordCheck8 -> 10 -> 12A -> ... -> 12H -> 12 -> PeriodicWordSmall` 是一条重计算 `decide +kernel` 串行链；不导入它们可让新模块独立秒级编译。
    - 不导入 `PeriodicNative.*` 确保零 `native_decide` 污染。
  - **库归属**：在 [lakefile.toml](file:///D:/langtonsant/lakefile.toml#L30-L39) 中应加入 **`PeriodicWords.roots`**（置于 `RecordSupport` / `RecordPair` 之后），**不可**加入 `LangtonsAnt.roots`（因为 `PeriodicWords` 依赖 `LangtonsAnt`，反之会造成库间循环依赖）。
  - **编译参数约束**：`PeriodicWords` 强制 `moreLeanArgs = ["-M1536", "-DwarningAsError=true"]`：
    - 峰值内存不得超过 1536 MB（纯符号证明远低于此限，切勿引入大规模 `decide +kernel`）。
    - 任何告警（未使用变量、冗余 `simp` 参数、未覆盖 linter 提示等）都会导致编译失败，开发阶段即应带上 `-DwarningAsError=true` 检查。

---

## 4. 安全的独立构建与验证命令

仓库在 `.lake/build/lib/lean/` 中已预编译好 `RecordPair.olean` 及全部前置依赖，因此开发和验证新模块**无需执行全局 `lake build`**。

在 `D:\langtonsant` 下的 PowerShell 中，使用仓库内置的固定工具链（若 `lake` 已在 `PATH` 且指向 Lean 4.36.0，也可将 `& 'D:\langtonsant\tools\lean-4.36.0-windows\bin\lake.exe'` 简写为 `lake`）：

1. **隔离检查单个新模块（不生成或重写其他 `.olean`，最安全、最快）**：
   ```powershell
   & 'D:\langtonsant\tools\lean-4.36.0-windows\bin\lake.exe' env lean -M1536 -DwarningAsError=true UnitDiagonalObstruction.lean
   ```
   （若拆分为两文件，先对底层文件执行 `lake build UnitDiagonalRank` 或逐个构建后再检上层文件。）

2. **将新模块加入 `lakefile.toml` 的 `PeriodicWords.roots` 后，仅构建该单模块 target**：
   ```powershell
   & 'D:\langtonsant\tools\lean-4.36.0-windows\bin\lake.exe' build UnitDiagonalObstruction
   ```

3. **运行公理审计与冒烟检查脚本**（确认仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`）：
   ```powershell
   & 'D:\langtonsant\tools\lean-4.36.0-windows\bin\lake.exe' env lean -M1536 -DwarningAsError=true scripts/UnitDiagonalChecks.lean
   ```

4. **源码静态信任边界复查**：
   ```powershell
   Select-String -Path D:\langtonsant\UnitDiagonal*.lean -Pattern 'sorry|admit|native_decide|\baxiom\b|unsafe|implemented_by|extern'
   ```

5. **严禁执行的高风险命令**：
   - **禁止**对 `SingleBlackEarly`、`SingleBlackFull`、`FreshRecovery` 或 `PeriodicNative` 执行 `lake build`（前两者每块耗内存 1–3 GB 且须用 `scripts/build_cells.py` 控并发；`FreshRecovery` 需约 15 分钟；`PeriodicNative.P34B*`/`P36B*` 重算需数十核时）。
   - 仅当所有新模块单测与审计通过后，才可视需要运行 `lake build PeriodicWords`（前提是既有 `PeriodicWordCheck*.olean` 未被修改或清除）。

---

## 5. 形式化关键陷阱与防错清单

1. **颜色与转向编码（`Bool` 极性易反）**：
   - 仓库约定：**`false` = 白格 = 右转 `R`**；**`true` = 黑格 = 左转 `L`**。
   - 在 Ke 论文与 `PROOF.md` 中，各翻译类的首个稳定访问读 `R`（白），然后 `R, L, R, L, ...` 交替；在 Lean 中对应 `w i = false`（秩 0）、`w i = true`（秩 1）、一般地 `w i = decide (rank % 2 = 1)`。

2. **到达朝向 vs 离开朝向（`step` 与 `wordTrace` 的时序对齐）**：
   - `step s` 的语义是：在 `s.pos` 读 `s.board s.pos`，按此色转向得 `d := turn (s.board s.pos) s.dir`，翻转 `s.pos`，移动到 `move s.pos d` 并令新朝向为 `d`。
   - 因此，对于时间 `n`（或相位 `i`）：
     - `(wordTrace w n).2` 是**进入** `wordPos w n` 时的**到达朝向**（即上一步离开 `wordPos w (n - 1)` 时的移动方向，对应入端口）；
     - `(wordTrace w (n + 1)).2 = turn (w n) (wordTrace w n).2` 是**离开** `wordPos w n` 时的**出发朝向**（对应出端口）。
   - 在定义某格的入边/出边与端口字时，务必严格区分 `inDir i := (wordTrace w i).2` 与 `outDir i := turn (w i) (wordTrace w i).2`（且对 `i = P - 1`，因 `(wordTrace w P).2 = .north = (wordTrace w 0).2`，`outDir (P - 1) = inDir 0` 精确闭合）。

3. **坐标系、位移符号与旋转约定**：
   - 仓库采用标准右手笛卡尔坐标：`north = (0, +1)`、`east = (+1, 0)`、`south = (0, -1)`、`west = (-1, 0)`。
   - `rotatePoint r` 将 `.north` 映到 `r`，因此 **`rotatePoint .east (x, y) = (y, -x)` 是顺时针 90°**，**`rotatePoint .west (x, y) = (-y, x)` 是逆时针 90°**。
   - 对规范单位对角位移 `v = (1, -1)`：
     - 四个旋转像依次为 `north ↦ (1, -1)`、`east ↦ (-1, -1)`、`south ↦ (-1, 1)`、`west ↦ (1, 1)`。
     - 不变横向层坐标为 `weight p = p.1 + p.2`；四方向单步对 `(weight, lift)`（其中 `lift p = p.1`）的影响必须按本仓库 `move` 逐一核对：
       - `.east`：`weight + 1`，`lift + 1`，稳定时间变化 `1 - P`；
       - `.north`：`weight + 1`，`lift + 0`，稳定时间变化 `+1`；
       - `.south`：`weight - 1`，`lift + 0`，稳定时间变化 `+1`；
       - `.west`：`weight - 1`，`lift - 1`，稳定时间变化 `1 + P`。
     - 特别核对极值层 `L_max` 的一步出入：若取极大层 `L_max`（`x + y` 最大），则到达 `L_max` 必由 `.east` 或 `.north`（使 `weight` 增 1），离开 `L_max` 必由 `.south` 或 `.west`（使 `weight` 减 1）。由白格右转（`false`）：`.east.right = .south`（合法，降层！），而 `.north.right = .east`（升层，矛盾！）；由黑格左转（`true`）：`.north.left = .west`（合法，降层！），而 `.east.left = .north`（升层，矛盾！）。结合白背景首次访问必读白（`false`）以及 `axisParity` 固定同层到达轴，**极大层 `L_max` 强制只能 `.east` 入、白格右转 `.south` 出**！而两步路径 `.east` 后接 `.south` 的净位移恰好为 `(1, 0) + (0, -1) = (1, -1) = v`，与 Ke 论文完全对齐（在 Lean 坐标系下极值层应取 **`weight` 最大层**，而非最小层；若取最小层则对应 `.west` 入 `.north` 出，净位移为 `(-1, 1) = -v`）。

4. **`ConsistentWord` 硬编码初始朝向 `.north` 带来的旋转陷阱**：
   - `rotateState r` 保持 `readColor` 不变，只旋转棋盘和朝向；但 `wordTrace w` 永远从 `((0, 0), .north)` 出发。
   - 因此，不能直接把 `rotateState` 套在 `ConsistentWord` 上来把 `(1, 1)` 变成 `(1, -1)`；必须先利用 `ConsistentWord.front_factor` 找到 4 方向中合适的起始相位 `a < P`，对 `w` 做**循环移位**（从而把初始朝向归一为 `.north` 且把 `wordDrift` 旋成 `(1, -1)`）。

5. **完整位移 vs 本原方向，以及 `P = 0` 边界**：
   - `UnitDiagonalDrift v` 限定的是单周期完整位移 `v = (±1, ±1)`，不是 `v` 约分后的本原方向（例如 `P = 104, v = (-2, -2)` 是合法的标准公路）。
   - `HighwayFrom s T 0 (0, 0)` 平凡成立；所有对外 `HighwayFrom` 定理应显式带 `(hP : 0 < P)`（与仓库已有接口保持一致），并在需要时用 `v ≠ (0, 0)` 另行推出 `0 < P`。

6. **`Int` 与 `Nat` 算术、`omega` 非线性限制与无 Mathlib 写法**：
   - `stableTime P w i : Int := (i : Int) - (P : Int) * (wordPos w i).1` 可能为负，务必保持在 `Int` 中运算，**避免**把它转为 `Nat` 或使用会截断的 `Nat` 减法。
   - 当 `v = (1, -1)` 时，周期平移量直接等于 `p.1 - q.1`，**完全不要**调用 `Int` 除法 `/`（`Int.ediv`）或 `priorShift`，以避免 `Int.ediv` 符号边界问题。
   - `omega` 无法直接求解两个变量相乘的非线性不等式（如 `k * (P : Int) < i`）。参考 [PeriodicWordCore.lean:166-179](file:///D:/langtonsant/PeriodicWordCore.lean#L166-L179)，遇到 `k * P` 时应拆分为 `k ≤ -1` / `k = 0` / `1 ≤ k` 并配合 `Int.mul_le_mul_of_nonneg_right` 化回线性再交给 `omega`。
   - 仓库无 Mathlib：凡涉及有限集计数、子集大小严格单调、映射双射与极值，均应沿用仓库既有范式——`List.range P` + `List.filter` + `List.Nodup` + `List.Perm`（`List.perm_ext_iff_of_nodup`）+ `List.max`（带非空证明或锚点）。

7. **可判定性与白背景必要性（防错校验）**：
   - 所有有限枚举集合（如 `layerPhases`, `priorPhases`）用 `decide` 对 `Point` / `Int` / `Direction` 的等式与不等式做布尔过滤均可自动找到 `Decidable` 实例，无需 `classical`；但对存在量词或反证法步骤可局部使用 `by_cases` / `Classical.byContradiction`（只引入标准 `Classical.choice`）。
   - 切勿遗漏“白背景（首访读 `false`）”前提：仅要求同格交替读色的无限背景允许 `P = 10`、位移 `(1, 1)` 的反例字 `1111010000`（见 [open-blocks-survey.md §4](file:///D:/langtonsant/research/open-blocks-survey.md#L86)）。因此证明中极大层“首次（且唯一一次）访问必读 `false`”这一步实质依赖 `ConsistentWord`（即 `FiniteSupport`），不可省去。
