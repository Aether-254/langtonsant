# 2026-11-23 新增 Lean 4 模块独立只读审计报告

**审计对象**：`D:\langtonsant` 仓库于 2026-11-23 新增的 25 个 Lean 4 模块（根目录 15 个，`PersistA/` 下 10 个），对照 `drafts/proof-status.md`（第 545–707 行）及相关研究记录（`research/brainstorm2-T2-diagonal-multiples-2026-11-22.md`、`research/brainstorm2-T3-width-2026-11-22.md`、`research/persist-A-width-2026-11-22.md`、`research/persist-B-diagonal-m3-2026-11-22.md`、`research/persist-C-periodic-tail-2026-11-23.md`）。

**审计范围**：本次不重复内核检查与公理核验（已由协调者确认全部编译通过且仅依赖标准三公理），专门审计内核检查无法捕获的语义层问题：陈述忠实度、定义与名称一致性、自然数截断减法/除法与越界偏移、假设空泛性与非空泛见证，以及 `drafts/proof-status.md` 的过度或失准宣称。

---

## 总览

- **Lean 模块代码层面**：在全部 25 个模块中，**未发现**隐蔽加强假设、削弱结论、名不副实定义、窗口差一错误、未受保护的 `Nat` 截断减法，或导致主定理空泛的不可满足前提。重点审查的 9 项核心定理（`BlackCountBound2.black_bound_suffix`、`BlackCountBound2.black_bound_finiteSupport`、`DirectionalBudget.directional_budget`、`DiagonalWinding.exists_rank_zero_lane`、`DiagonalWinding.strict_period_bound`、`RootWord.root_word`、`RootWord.prime_drift_least`、`PersistA.TwoGateDecomposition.exists_two_gate_decomposition`、`PersistA.GateRebase.exists_gate_rebase_sharedBoundary`）陈述均忠实于纸面命题。
- **`drafts/proof-status.md` 层面**：发现 **3 处需修正**与 **1 处存疑（轻微歧义）**，均属于文档摘要对定理适用范围或措辞的失准，而非 Lean 定理本身的语义缺陷；另附 3 处因按时间追加形成的轻微文档陈旧记录。

### 模块审计汇总表

| 编号 | 模块 | 综合判定 | 文件内非空泛见证 | 备注 |
| --- | --- | --- | --- | --- |
| 1 | `MixedWakeDefect.lean` | 无问题 | 有（`stdHighwaySE`） | 未发现问题 |
| 2 | `DirectionTableTranslation.lean` | 无问题 | 部分（`F_zero` 仅见证零平移） | 未发现问题 |
| 3 | `DiagonalRankZeroLane.lean` | 无问题 | 有（`standard_rank_zero_witness`） | 未发现问题 |
| 4 | `DiagonalWinding.lean` | 无问题 | 复用所导入的 `DiagonalRankZeroLane` 见证 | 重点审查项通过 |
| 5 | `RootWord.lean` | 需修正（仅 `proof-status.md`） | 有（`stdHighwaySE_power_nonvacuity`） | Lean 无问题；`drafts/proof-status.md:592` 推论失准 |
| 6 | `WidthLemmas.lean` | 无问题 | 有（`stdHighwaySE_nonvacuous`） | 未发现问题 |
| 7 | `DiagonalReturnOrder.lean` | 无问题 | 有（`stdHighwaySE_nonvacuity`） | 未发现问题 |
| 8 | `WidthCutSum.lean` | 无问题 | 有（`stdHighwaySE_nonvacuous`） | 未发现问题 |
| 9 | `DiagonalSegments.lean` | 无问题 | 有（`stdHighwaySE_nonvacuity`） | 未发现问题 |
| 10 | `DiagonalTablePeriod.lean` | 无问题 | 无（前提可由 `stdHighwaySE` 二次幂满足） | 未发现问题 |
| 11 | `RootTail.lean` | 存疑（仅 `proof-status.md`） | 无（纯周期算术，平凡可满足） | Lean 无问题；`drafts/proof-status.md:672` 省略前句前提 |
| 12 | `WidthDefects.lean` | 需修正（仅 `proof-status.md`） | 有（`stdHighwaySE_nonvacuous` 等） | Lean 无问题；`drafts/proof-status.md:618` 遗漏 `runEdgeOccurrence_perm` 的 `botLayer ≤ t` 前提 |
| 13 | `BlackCountBound.lean` | 无问题 | 有（`blank_bound_example` 等） | 未发现问题 |
| 14 | `BlackCountBound2.lean` | 无问题 | 复用所导入的 `BlackCountBound` 见证 | 重点审查项通过 |
| 15 | `DirectionalBudget.lean` | 无问题 | 有（`blank_budget_all` 等） | 重点审查项通过 |
| 16 | `PersistA/TimingCircuit.lean` | 无问题 | 无（纯整数/归纳算术，平凡可满足） | 未发现问题 |
| 17 | `PersistA/TranslationShift.lean` | 无问题 | 无（前提由 `stdHighwaySE` 满足） | 未发现问题 |
| 18 | `PersistA/GatePath.lean` | 无问题 | 下游由 `GateRebase` 见证 | 未发现问题 |
| 19 | `PersistA/TwoLaneCycle.lean` | 需修正（主要为 `proof-status.md`） | 下游由 `GateRebase` 见证 | `drafts/proof-status.md:629` 将 `maximal_cycle_four` 误述为“极大环长为 4”，且模块仅证周期整除 4 未显式打包 `n = 4` |
| 20 | `PersistA/FirstVisitMap.lean` | 无问题 | 下游由 `GateRebase` 见证 | 未发现问题 |
| 21 | `PersistA/FiniteOrbitCycle.lean` | 无问题 | 无（抽象有限轨道引理，平凡可满足） | 未发现问题 |
| 22 | `PersistA/FirstVisitCycle.lean` | 无问题 | 下游由 `GateRebase.stdCore` 见证 | 未发现问题 |
| 23 | `PersistA/TwoGateDecomposition.lean` | 无问题 | 下游由 `GateRebase` 见证 | 重点审查项通过 |
| 24 | `PersistA/SharedBoundary.lean` | 无问题 | 有（`stdHighwaySE_nonvacuity`） | 未发现问题 |
| 25 | `PersistA/GateRebase.lean` | 无问题 | 有（`stdHighwaySE_nonvacuity`、`stdCore`） | 重点审查项通过 |

---

## 分模块逐项审计

### 1. `MixedWakeDefect.lean`

- **判定**：**无问题**
- **核查要点**：
  - `mixed_step_defect`（`MixedWakeDefect.lean:23-36`）仅要求末朝向复原 `(wordTrace w P).2 = .north`、完整漂移 `wordDrift P w = (2, -2)` 及偶层条件 `t % 2 = 0`，甚至不依赖 `ConsistentWord`，与 `research/brainstorm2-T3-width-2026-11-22.md:53-70` 完全一致。公式中各项均为 `Nat` 加法后取 `% 2`，无截断减法。
  - `stdHighwaySE_defect`（`MixedWakeDefect.lean:41-48`）、`stdHighwaySE_not_pureOddWake`（`MixedWakeDefect.lean:52-57`）与 `stdHighwaySE_interfaces`（`MixedWakeDefect.lean:64-70`）以纯内核计算给出真实标准字的显式见证，非空泛性充分。
  - `drafts/proof-status.md:545-557` 的叙述与代码完全一致，未发现问题。

### 2. `DirectionTableTranslation.lean`

- **判定**：**无问题**
- **核查要点**：
  - `TableEntry`（`DirectionTableTranslation.lean:21-24`）以存在 `i ∈ Drift.classPhases v P w c` 且 `stableRank P w i = r ∧ inDir w i = d` 定义；由于 `Drift.stableRank_bijection_on_class`（`DriftRank.lean:445-454`）保证同一类内稳定秩与 `[0, len)` 一一对应，故 `PreservesTables v P w b`（`DirectionTableTranslation.lean:29-30`）对全部 `c : Point`、`r : Nat`、`d : Direction` 成立当且仅当平移 `b` 在所有类（含空类）上保持类长及按稳定秩排列的入射方向列表，忠实于 `research/brainstorm2-T2-diagonal-multiples-2026-11-22.md:63-73`。
  - `F_succ`（`DirectionTableTranslation.lean:176-221`）与对角特化 `diagonal_F_succ`（`DirectionTableTranslation.lean:224-230`）对任意 `i < P` 成立，无多余假设。
  - 非空泛见证：`F_zero`（`DirectionTableTranslation.lean:233-240`）和 `preservesTables_zero`（`DirectionTableTranslation.lean:32-35`）仅见证了零平移 `b = (0, 0)`；文件内不含非零 `b` 的见证（真实非零实例可取标准字二次幂 `P = 208, v = (4, -4), b = (2, -2)`）。`drafts/proof-status.md:561` 已明确写明仅以零平移作非空泛检查，无过度宣称。
  - 未发现问题。

### 3. `DiagonalRankZeroLane.lean`

- **判定**：**无问题**
- **核查要点**：
  - `TopOccupied m P w`（`DiagonalRankZeroLane.lean:18-20`）对全部 `r : Int` 要求顶层类长度非零；在 `m > 0` 且周期性下与 `0 ≤ r < m` 等价。
  - `top_occupied_length_one`（`DiagonalRankZeroLane.lean:22-31`）、`first_inner_candidates`（`DiagonalRankZeroLane.lean:33-37`）、`first_inner_port_ranks`（`DiagonalRankZeroLane.lean:41-56`）、`rank_zero_time_lt_rank_two`（`DiagonalRankZeroLane.lean:60-72`）及纯求和引理 `early_of_negative_sum`（`DiagonalRankZeroLane.lean:86-98`）均忠实于定义与纸面陈述。由 `DiagonalMultipleLanes.incoming_classPortWord` / `outgoing_classPortWord`（`DiagonalMultipleLanes.lean:383-427`），深度 1 处 `laneAlpha` 的 `true` 位恰对应 `.south` 入射（上入口），`laneBeta` 的 `true` 位恰对应 `.east` 出射（上出口），与 `first_inner_port_ranks` 一致。
  - 文件内含完整标准字见证 `standard_top_classes` 至 `standard_rank_zero_witness`（`DiagonalRankZeroLane.lean:102-155`）。
  - 注：`drafts/proof-status.md:566-568` 的旧标题“部分”及“一般定理未完成”系后续在同一节下追加 `DiagonalWinding.lean`（`drafts/proof-status.md:571`）所致，属保守表述而非过度宣称。未发现问题。

### 4. `DiagonalWinding.lean`（重点审查）

- **判定**：**无问题**
- **重点定理审查**：
  - `strict_period_bound`（`DiagonalWinding.lean:41-63`）：假设为 `ConsistentWord P w` 与 `wordDrift P w = diagDrift m`，结论为 `2 * m < P`。不要求 `TopOccupied`，不要求最小周期，亦不额外要求 `0 < m`（已由 `ConsistentWord` 的非零漂移隐含）。证明用 `travelSlack w i = i - ((wordPos w i).1 - (wordPos w i).2)` 的单调性及最低层北向出射增量 2，完全忠实于 `research/brainstorm2-T2-diagonal-multiples-2026-11-22.md:45-47`。
  - `winding_identity`（`DiagonalWinding.lean:288-296`）：虽然 `upperArrivalRank`/`upperDepartureRank`（`DiagonalWinding.lean:66-69`）仅按 `a.headD false` 定义，但 `upperArrival_spec`（`DiagonalWinding.lean:143-159`）与 `upperDeparture_spec`（`DiagonalWinding.lean:162-178`）已独立证明在 `TopOccupied` 下，所选相位确为该通道**唯一**的 `.south` 入射与 `.east` 出射；`upper_bridge`（`DiagonalWinding.lean:182-215`）与 `upper_bridge_time`（`DiagonalWinding.lean:249-262`）完整保留跨提升边界的 `((r + 1) / m - r / m) * P` 补偿。求和式 `((List.range m).map (laneDelta m P w)).sum = 2 * (m : Int) - (P : Int)` 与 T2 命题 1 的绕行恒等式完全一致。
  - `exists_rank_zero_lane`（`DiagonalWinding.lean:319-338`）：假设 `ConsistentWord P w`、`0 < m`（冗余但无害）、`wordDrift P w = diagDrift m`、`TopOccupied m P w`，结论存在 `r < m` 使第一内层 `laneAlpha` 为 `word100` 或 `word1000`（结合 `DiagonalRankZeroLane.first_inner_port_ranks`，即上侧入射在秩 0）。
  - 非空泛性：本文件未单列见证定理，但直接导入 `DiagonalRankZeroLane.standard_rank_zero_witness`（`DiagonalRankZeroLane.lean:145-155`），完整满足上述全部定理的前提。
  - `drafts/proof-status.md:571-579` 无过度宣称，未发现问题。

### 5. `RootWord.lean`（重点审查）

- **判定**：**需修正（仅 `drafts/proof-status.md:592` 推论表述；Lean 代码本身无问题）**
- **Lean 代码重点定理审查（未发现问题）**：
  - `ReadPeriod`（`RootWord.lean:21-22`）与 `LeastReadPeriod`（`RootWord.lean:52-53`）定义于全体 `Nat`，文件头部（`RootWord.lean:7-9`）已明确说明 `ConsistentWord P w` 仅约束前 `P` 项，故对有限字须作用于 `repeatWord P w`。
  - `root_word`（`RootWord.lean:180-189`）：在 `ConsistentWord P w`、`0 < P`（由 `ConsistentWord` 隐含，无害）、`0 < q`、`q ∣ P`、`ReadPeriod q w` 下，**证明**而非假设了 `q` 步恢复朝向（`period_heading`，`RootWord.lean:128-142`），并导出 `ConsistentWord q w` 与精确漂移关系 `wordDrift P w = scalePoint (wordDrift q w) ((P / q : Nat) : Int)`（因 `q ∣ P`，`P / q` 无截断误差）。
  - `root_word_diagonal`（`RootWord.lean:193-215`）、`least_root_diagonal`（`RootWord.lean:242-259`）与 `odd_drift_root`（`RootWord.lean:282-303`）同时证明整除性 `(P / q) ∣ m`，故 `m / (P / q)` 为精确整除，无截断误差；且 `least_root_diagonal` 将 `ConsistentWord q` 还原回原字 `w`。
  - `Prime`（`RootWord.lean:218-219`）为标准自然数素性定义（`2 ≤ m` 且仅有因子 `1, m`）。`prime_drift_least`（`RootWord.lean:263-278`）对任意 `r > 0`（不限于 `P` 的约数）均排出更短周期，给出 `LeastReadPeriod P (repeatWord P w)`。
  - 非空泛见证：`stdHighwaySE_power_nonvacuity`（`RootWord.lean:330-341`）与 `stdHighwaySE_minimal`（`RootWord.lean:345-359`）具体实例化了 `P = 208, q = 104` 的取根；此外因 `Prime 2` 成立，`stdHighwaySE`（`P = 104, m = 2`）直接使 `prime_drift_least` 非空泛。（`odd_drift_root` 无具体实例属预期，因目前不知任何奇数对角自洽字，猜想其不存在。）
- **`drafts/proof-status.md:592` 发现的问题（需修正）**：
  - **位置**：`drafts/proof-status.md:592`。
  - **原文**：“**推论**：任何完整漂移 `(3, −3)`（或任意奇数倍、任意素数倍）的自洽字都直接是目标 B 的反例，无需另加最小周期假设；目标 B 等价于：任意完整漂移 `(m, −m)` 自洽字的最小根，其漂移倍数恰为 2（单位倍数已排除）。这是等价改写，不是目标 B 的证明。”
  - **具体问题**：
    1. **“任意素数倍”包含 `m = 2`**：按 `RootWord.Prime`（`RootWord.lean:218-219`），`2` 是素数，完整漂移 `(2, −2)` 是已知的标准 104 步公路（`stdHighwaySE`），**不是**目标 B（排除最小周期下 `m ≥ 3`）的反例。对照原纸面记录 `research/persist-B-diagonal-m3-2026-11-22.md:724-726`，原文仅对所有素数 `m ≥ 2` 断言最小周期性，并未把 `m = 2` 列为目标 B 反例。
    2. **“任意奇数倍……都直接是目标 B 的反例，无需另加最小周期假设”不严谨**：其一，`m = 1` 也是奇数（虽已被 `UnitDiagonal` 排除，表述上仍应限定 `m ≥ 3`）；其二，对**奇合数** `m`（如 `m = 9`），原字所选周期 `P` 未必是最小周期（例如 `m = 3` 反例的三次幂），只有经 `least_root_diagonal` 与 `odd_drift_root` **取最小根后**才必得奇数倍 `≥ 3` 的最小周期反例（`research/persist-B-diagonal-m3-2026-11-22.md:726` 原文准确表述为“故经取根必给出目标 B 反例”）。
    3. 后半句“目标 B 等价于……”是纸面等价改写，并未在 `RootWord.lean` 中形式化为 Lean 定理，建议显式注明。
  - **修改建议**：将 `drafts/proof-status.md:592` 改为：“**推论**：任何完整漂移为 `(3, −3)` 或任意**奇素数倍（素数 `m ≥ 3`）**的自洽字，其所选 `P` 已自动为最小正读周期，直接构成目标 B 的反例；任何**奇数倍 `m ≥ 3`** 的自洽字经 `least_root_diagonal` 与 `odd_drift_root` **取最小根后**仍为奇数倍且 `≥ 3`，同样给出目标 B 的反例。纸面等价改写（未在 `RootWord.lean` 中单列等价定理）：目标 B 等价于……”。

### 6. `WidthLemmas.lean`

- **判定**：**无问题**
- **核查要点**：
  - `eta`（`WidthLemmas.lean:22-23`）、`eta_eq_stableTime`（`WidthLemmas.lean:26-37`）、`path_eta_difference`（`WidthLemmas.lean:50-62`）忠实于 `research/persist-A-width-2026-11-22.md:1113-1117`，完整保留通道偏移和跨周期接缝。
  - `eta_gap_pos_multiple_eight`（`WidthLemmas.lean:119-136`）与 `adjacent_rankEta_gap`（`WidthLemmas.lean:225-240`）严格证明同类相邻 `eta` 间隔为正的 8 的倍数，未附加无根据的上界。
  - `throughCharge`（`WidthLemmas.lean:150-151`）与 `boundary_rank_gap_expansion`（`WidthLemmas.lean:208-222`）对 `hm : 0 < classMult P w t r` 保护了 `classMult - 1` 的自然数减法，索引 `chargePrefix (j + 1)` 与第 37 轮公式 `(37.1)`（`persist-A:1139-1144`）精确对齐；`chargePrefix_full_eq_counts`（`WidthLemmas.lean:256-269`）将其还原为实际边界端口差。
  - 非空泛见证：`stdHighwaySE_rank_data`（`WidthLemmas.lean:275-284`）与 `stdHighwaySE_nonvacuous`（`WidthLemmas.lean:288-294`）。
  - 注：`drafts/proof-status.md:604` 仍留有“第 36 轮的完整切口求和式、第 33–35 轮的游程与缺陷计数仍未形式化”的旧边界句，紧随其后的 `L606` 与 `L614` 已补齐，属按时间追加遗留，非过度宣称。未发现问题。

### 7. `DiagonalReturnOrder.lean`

- **判定**：**无问题**
- **核查要点**：
  - `ZeroReturn`（`DiagonalReturnOrder.lean:28-30`）精确对应 `p[i] = q[j] + 1`；`zeroReturn_strict_order`、`zeroReturn_port_eq_iff`、`zeroReturn_adjacent_first`、`zeroReturn_cycle_constant`（`DiagonalReturnOrder.lean:56-146`）忠实于 `research/persist-B-diagonal-m3-2026-11-22.md` 第 15–17 轮。
  - `UpperReturn`（`DiagonalReturnOrder.lean:151-161`）携带真实 `ContinuousPhasePath`、正长度 `0 < len`、精确物理起点 `laneCell (topLayer P w - n) r`、同格物理返回 `p.pos w len = p.pos w 0`、严格中间层分离 `∀ k, 0 < k → k < len → layer (p.pos w 0) < layer (p.pos w k)`（由此自动排除中途返回同一格，确为真正的**首次**物理返回，且排除 `len = 1` 的退化情形）以及出入端口编号。
  - 非空泛见证：`stdHighwaySE_depth8_alpha`、`stdHighwaySE_return_zero`（`1 → 9`，端口 `0 → 0`）、`stdHighwaySE_return_one`（`9 → 85`，端口 `1 → 1`）与 `stdHighwaySE_nonvacuity`（`DiagonalReturnOrder.lean:211-275`）同时满足相邻返回定理的前提。
  - `drafts/proof-status.md:642-653` 叙述准确，未发现问题。

### 8. `WidthCutSum.lean`

- **判定**：**无问题**
- **核查要点**：
  - `edgeCut`（`WidthCutSum.lean:88-89`）由 `edgeCut_eq_min`（`WidthCutSum.lean:103-107`）证得等于相邻两层最小值，`upperWeight`（`WidthCutSum.lean:92-93`）准确标记切口 `t` 及以上的全部边。
  - `boundaryTime`（`WidthCutSum.lean:100-101`）经 `boundaryTime_eq_through_sums`（`WidthCutSum.lean:161-173`）确证等于层 `t` 上向下直穿与向上直穿事件的 `eta` 和之差。
  - `sumAbove`（`WidthCutSum.lean:413-414`）利用 `cutFlow_eq_zero_of_top_le`（`WidthCutSum.lean:363-374`）在 `t ≥ topLayer` 时自然取空和 0，在 `t < topLayer` 时精确覆盖 `s = t, …, topLayer - 1`，无差一错误。
  - `boundaryTime_eq_length_transport`（`WidthCutSum.lean:199-210`）与 `boundaryTime_eq_cut_sums`（`WidthCutSum.lean:449-457`）对任意 `t : Int`（包括 `t < botLayer` 时两端均为 0）成立，且在朝北字坐标系中 `cutSign s = (-1)^s`（`σ = +1`）符号核对无误，完整覆盖 `L = P` 情形。
  - 非空泛见证：`stdHighwaySE_cut_data`（`WidthCutSum.lean:470-475`）与 `stdHighwaySE_nonvacuous`（`WidthCutSum.lean:478-487`）。
  - `drafts/proof-status.md:606-612` 叙述准确，未发现问题。

### 9. `DiagonalSegments.lean`

- **判定**：**无问题**
- **核查要点**：
  - `Excursion`（`DiagonalSegments.lean:175-181`）要求 `1 < len`、两端在层 `L`、内部严格高于 `L`，`len_le_period`（`DiagonalSegments.lean:459-468`）允许 `len = P`。
  - 第 21 轮：`Excursion.rank_edge`（`DiagonalSegments.lean:472-509`）、`blocks_rank_edge`（`DiagonalSegments.lean:280-316`）与 `physical_cycle_weight_negative`（`DiagonalSegments.lean:574-593`）忠实于 `research/persist-B-diagonal-m3-2026-11-22.md:1001-1004`，其中 `path_same_block_order`（`DiagonalSegments.lean:393-412`）在 `len = P` 时同样成立。
  - 第 23 轮：`ParentChain`（`DiagonalSegments.lean:678-688`）、`exists_parentChain`（`DiagonalSegments.lean:751-773`）、`boundary_complete`（`DiagonalSegments.lean:803-831`）、`unique`（`DiagonalSegments.lean:863-868`）、`parent_complete`（`DiagonalSegments.lean:872-893`）、`zero_parent_endpoint`（`DiagonalSegments.lean:981-1014`）、`all_zero_count_two`（`DiagonalSegments.lean:1016-1024`）及 `child_displacement`（`DiagonalSegments.lean:1060-1108`，参数 `n` 对应新加父层的深度 `d`，且空链 `c.len = 2, count = 0` 亦被正确覆盖）全部与 `persist-B:1028-1038` 精确吻合。
  - 第 24 轮：`splice_separated` / `copiesSeparated_splice`（`DiagonalSegments.lean:134-172`）、`bridge_copy_increment_x`（`DiagonalSegments.lean:349-362`）、`contraction_weight` / `contracted_rank_edge`（`DiagonalSegments.lean:366-390`）、`Excursion.zero_no_bridge_cycle`（`DiagonalSegments.lean:1133-1140`，甚至对仅相位匹配的闭链也成立）及 `upperReturn_forced_bridge`（`DiagonalSegments.lean:1198-1209`）忠实于 `persist-B:1042-1047`。
  - 第 32 轮：`east_entries_same_y_parity`（`DiagonalSegments.lean:1213-1227`）仅需 `ConsistentWord P w`（利用 `drift_sum_even`），对任意正负周期副本成立。
  - 非空泛见证：`stdChild`、`stdChain`、`stdChain_parents_zero`、`stdHighwaySE_nonvacuity`、`stdHighwaySE_rank_edge`（`DiagonalSegments.lean:1232-1320`）。
  - `drafts/proof-status.md:655-666` 准确标注了已证与未证范围，未发现问题。

### 10. `DiagonalTablePeriod.lean`

- **判定**：**无问题**
- **核查要点**：
  - `F_eq_shift`（`DiagonalTablePeriod.lean:38-49`）、`tables_read_period`（`DiagonalTablePeriod.lean:51-62`）、`diagonal_shift_nonzero`（`DiagonalTablePeriod.lean:64-84`）与 `diagonal_tables_not_least`（`DiagonalTablePeriod.lean:86-97`）忠实于 `research/persist-B-diagonal-m3-2026-11-22.md:1599-1610`（第 43 轮）。
  - `diagonal_tables_not_least` 中 `hv : Not ((m, -m) = (0, 0))` 与 `hm : 0 < m` 略有冗余，无损结论。
  - 非空泛性：本文件未含具体见证定理，但前提确实可满足（例如 `stdHighwaySE` 的二次幂 `P = 208, m = 4, a = 2`，平移 `(2, -2)` 保持全体有序表，且 `F 0 = 104`）。
  - `drafts/proof-status.md:670` 已显式强调“这种平移的存在性没有证明”，未发现问题。

### 11. `RootTail.lean`

- **判定**：**存疑（仅 `drafts/proof-status.md:672` 简写歧义；Lean 代码本身无问题）**
- **Lean 代码核查（未发现问题）**：
  - `period_of_eventual_period`（`RootTail.lean:21-35`）、`eventual_period_bounds_least`（`RootTail.lean:37-40`）、`shift_of_eventual`（`RootTail.lean:52-65`）、`shifts_commensurate`（`RootTail.lean:67-75`）、`standard_tail_bounds_root`（`RootTail.lean:77-86`）、`tail_drift_bounds_root`（`RootTail.lean:88-100`）与 `tail_two_exact_root`（`RootTail.lean:102-114`）全部忠实于 `research/persist-B-diagonal-m3-2026-11-22.md:1536-1552, 1593`（第 41、42 轮）。
  - 非空泛性：文件内无显式见证，但作为纯周期算术引理，前提显然可满足（如 `w = stdHighwaySE, P = q = 104, N = 0, m = u = 2`）。
- **`drafts/proof-status.md:672` 发现的轻微歧义（存疑）**：
  - **位置**：`drafts/proof-status.md:672`。
  - **原文**：“若最小周期为 `P` 的序列最终有周期 `q`，则 `P ≤ q`；若坐标 `x` 每 `P` 步前进 `m`、最终每 `q` 步前进 `u ≥ 0`，则 `m ≤ u`；`u = 2`、`m ≥ 2` 时 `m = 2` 且 `P = q`（`tail_two_exact_root`）。”
  - **具体问题**：分号后的后半句若单独理解，未写明仍须满足前一句的“序列 `w` 最小周期为 `P` 且最终有正周期 `q`（`0 < q`）”。仅有坐标函数 `x` 的两个平移条件并不足以推出 `P ≤ q` 或 `m ≤ u`（例如 `x(n) = 2n` 取 `P = 2, m = 4, q = 1, u = 2`）。Lean 定理 `tail_drift_bounds_root`（`RootTail.lean:88-93`）与 `tail_two_exact_root`（`RootTail.lean:102-107`）均正确包含 `hleast : LeastReadPeriod P w`、`hq : 0 < q` 及 `hread`。
  - **修改建议**：将 `drafts/proof-status.md:672` 中后半句改为“在此同一 `P, q`（`q > 0`）前提下，若坐标 `x` 每 `P` 步前进 `m`、最终每 `q` 步前进 `u ≥ 0`，则 `m ≤ u`；……”。

### 12. `WidthDefects.lean`

- **判定**：**需修正（仅 `drafts/proof-status.md:618` 前提范围遗漏；Lean 代码本身无问题）**
- **Lean 代码核查（未发现问题）**：
  - `UpperRun`（`WidthDefects.lean:446-453`）精确刻画从层 `t` 向上离开至首次回到层 `t` 的真实游程，正确允许 `len = P`（对应第 40 轮勘误，`persist-A:1227-1237`）；`runEndPos`（`WidthDefects.lean:850-851`）保留了 `(i + runLength) / P` 的周期提升进位，使物理同格返回/非返回计数（`returnCount`、`nonreturnCount`）跨接缝依然精确。
  - `wakeCharge`（`WidthDefects.lean:101-103`）通过 `wakeCharge_eq_event_counts`（`WidthDefects.lean:214-237`）与 `local_flow_balance`（`WidthDefects.lean:240-250`）验证符号与定义完全准确。
  - `layerSum`（`WidthDefects.lean:264-266`）闭区间覆盖 `[botLayer, topLayer]`（长度 `(topLayer - botLayer).toNat + 1`），无差一错误；`same_colour_endpoint_defect`（`WidthDefects.lean:770-776`）、`secondMoment_defect_expansion`（`WidthDefects.lean:779-788`）、`nonreturn_discrete_derivative_bound`（`WidthDefects.lean:895-903`）、`return_incidence_bounds`（`WidthDefects.lean:921-930`）均对任意 `t : Int` 成立。
  - `runEdgeOccurrence_perm`（`WidthDefects.lean:1088-1111`）、`sum_runLength_eq_twice_cut_sum`（`WidthDefects.lean:1212-1217`）与 `runTransport_eq_signed_cut_sum`（`WidthDefects.lean:1205-1209`）均正确加入 `hbot : botLayer P w <= t`，并附标准字 `t = -2` 的内核反例 `stdHighwaySE_below_support`（`WidthDefects.lean:1290-1296`）。
  - 非空泛见证：`fullPeriodControl_run` / `fullPeriodControl_not_consistent`、`stdHighwaySE_defect_data`、`stdHighwaySE_below_support`、`stdHighwaySE_nonvacuous`（`WidthDefects.lean:1244-1307`）。
- **`drafts/proof-status.md:618` 发现的问题（需修正）**：
  - **位置**：`drafts/proof-status.md:618`。
  - **原文**：“游程与上方边一一对应（`runEdgeOccurrence_perm`），游程总长 `= 2 Σ f`，总位移 `= Σ (−1)^s f_s`（`runTransport_eq_signed_cut_sum`）。**后两式需要 `botLayer ≤ t`**……”
  - **具体问题**：实际上，所列**三式全部**都需要 `botLayer ≤ t`，包括第一个 `runEdgeOccurrence_perm`（`WidthDefects.lean:1090` 显式要求 `hbot : botLayer P w <= t`）。当 `t < botLayer` 时边界无任何游程起点（`runEdgeOccurrences = []`），但上方边有 `P` 条，因此双射同样不成立。写“后两式”易使读者误以为 `runEdgeOccurrence_perm` 无此前提。
  - **修改建议**：将“**后两式需要 `botLayer ≤ t`**”改为“**以上三式（`runEdgeOccurrence_perm`、游程总长及总位移）均需要 `botLayer ≤ t`**”。

### 13. `BlackCountBound.lean`

- **判定**：**无问题**
- **核查要点**：
  - `recentCells s W n`（`BlackCountBound.lean:47-49`）用 `unique` 去重，精确枚举 `{ (run s j).pos | j < n ∧ n ≤ j + W }`；当 `W ≤ n` 时恰为 `[n - W, n)` 的 `W` 步，与 `research/persist-C-periodic-tail-2026-11-23.md:77` 一致，无差一或重复计数。
  - `cacheLive`（`BlackCountBound.lean:170-171`）、`cacheEviction`（`BlackCountBound.lean:173-175`）、`cacheMissBit`（`BlackCountBound.lean:177-178`）均不重复计数且忠实于 (C1) 定义。`cacheEviction_position`（`BlackCountBound.lean:213-223`）中若 `p ∈ cacheEviction s W n`，必自动有 `W ≤ n`，故 `n - W` 无截断误差。
  - `cache_balance`、`cache_balance_interval`、`black_cache_balance`、`black_bound_of_event_bound` 全部采用有符号整数 `Int` 运算，并对 `FiniteState` 的黑格列表长度显式要求 `hnd : s.black.Nodup`（由 `FiniteState.nodup_run` 保持），防止重复项虚增基数。
  - `sumFrom`（`BlackCountBound.lean:234-236`）在 `[a, a + N)` 上求和，故 `missCount s W W (N - W)` 在 `W ≤ N` 时精确对应 `W ≤ n < N` 的 `E_W(N)`。
  - 非空泛见证：`blank_cache_balance_example` 与 `blank_bound_example`（`BlackCountBound.lean:329-337`）。
  - `drafts/proof-status.md:676-683` 叙述忠实，明确标出 `black_bound_of_event_bound` 为条件归约。未发现问题。

### 14. `BlackCountBound2.lean`（重点审查）

- **判定**：**无问题**
- **重点定理审查**：
  - 证明链条忠实性审查：
    1. `cacheState_step` / `cacheState_run`（`BlackCountBound2.lean:44-89`）：在既无缓存失配（`cacheMissBit = false`，注意允许读到窗口外的白格）也无黑格淘汰（`cacheEviction = []`）的区间上，有限缓存状态 `(cacheState s W a).toState` 按真实蚂蚁步法演化至 `(cacheState s W (a + k)).toState`。
    2. `cacheState_rigid_of_suffix`（`BlackCountBound2.lean:496-512`）：在 `W ≤ n`、`W ≤ m` 下（避免了 `readSuffix` 在 `n < W` 时的截断），相同的长 `W` 布尔读色后缀决定两时刻缓存状态相差一个刚体运动（旋转加平移），无需对更早棋盘作任何假设，状态空间大小精确为 `2 ^ W`（`boolean_suffix_universe_length`，`BlackCountBound2.lean:235-237`）。
    3. `finite_no_rigid_return`（`BlackCountBound2.lean:436-448`）：对任意无重复有限状态，刚体回返迭代 4 次得平移回返（`rigid_four`，`BlackCountBound2.lean:423-434`），构成零净增长的有限支撑公路，与 `periodic_tail_eight_le_growth` 矛盾。
    4. `event_in_suffix_block`（`BlackCountBound2.lean:566-604`）与 `event_bound_suffix`（`BlackCountBound2.lean:628-638`）：鸽巢原理使用 `2^W + 1` 个时刻 `a, …, a + 2^W`（间隔至多 `2^W` 步，无差一错误），且适用于任意初态 `s : State`（不限于有限支撑），从而在 `[a, a + n)` 上强制至少 `n / 2^W` 次事件。
  - `black_bound_suffix`（`BlackCountBound2.lean:641-649`）：
    - 假设：`s : FiniteState`、`hnd : s.black.Nodup`、`hW : 0 < W`、`hN : W <= N`。
    - 结论：`((s.run W).black.length : Int) - (W : Int) + ((N - W) / 2 ^ W : Nat) - 2 * missCount s.toState W W (N - W) <= ((s.run N).black.length : Int)`。
    - 检查：`hN : W ≤ N` 杜绝 `N - W` 的自然数截断；`((N - W) / 2 ^ W : Nat)` 精确等于 `⌊(N - W) / 2^W⌋`；外层加减全为 `Int`；`missCount s.toState W W (N - W)` 精确统计 `W ≤ n < N`。与 `research/persist-C-periodic-tail-2026-11-23.md:116` 的 (C2) 逐字相符。
  - `black_bound_finiteSupport`（`BlackCountBound2.lean:680-691`）：
    - 适用于任意 `s : State` 与 `FiniteSupport s.board`，以及任意无重复精确黑格枚举 `BW, BN : List Point`。`finiteSupport_representation`（`BlackCountBound2.lean:652-666`）结合 `finiteSupport_run` 保证对每个有限支撑初态此类 `BW, BN` 必然存在，前提绝非空泛。
  - 非空泛性：本文件内未单独重复写具体轨线实例，但导入了 `BlackCountBound.blank_bound_example` 且对 `finiteBlank`（任何 `1 ≤ W ≤ N`）平凡可实例化。
  - `drafts/proof-status.md:685-693` 准确描述了上述两定理及无条件边界。未发现问题。

### 15. `DirectionalBudget.lean`（重点审查）

- **判定**：**无问题**
- **重点定理审查**：
  - 定义忠实度审查：
    - `UnitProjection s f`（`DirectionalBudget.lean:96-98`）要求沿轨迹每步变化在 `[-1, 1]` 内（甚至弱于全平面 1-Lipschitz，且 `x_unitProjection` 已见证 `f(x,y) = x` 满足之）。
    - `progressDefect`（`DirectionalBudget.lean:31-32`）用 `(1 - (h (k + 1) - h k)).toNat` 精确实现 `max(0, 1 - (h_{k+1} - h_k))`；`totalDefect`（`DirectionalBudget.lean:34-36`）精确求和 `k < K`。
    - `window L = L * (4 * L + 2)`（`DirectionalBudget.lean:103`）；`ceilBlocks N L = (N + L - 1) / L`（`DirectionalBudget.lean:105`），经检验在 `hL : 0 < L` 下对全体 `N : Nat`（含 `N = 0` 时 `(L - 1) / L = 0`）均精确等于 `⌈N / L⌉`，无自然数截断错误。
    - `firstBlack`（`DirectionalBudget.lean:172-173`）与 `repeatedMiss`（`DirectionalBudget.lean:180-181`）将所有失配拆为初始黑格首访（由 `firstBlack_count_le` 以 `(unique s.black).length` 精确控住，不因列表重复项放大）与重复黑读失配。
    - `backward_charging`（`DirectionalBudget.lean:70-94`）中的自然数减法 `k - j` 与 `D k - D j` 均由 `j < k` 及单调性 `hmono` 保证非负，无截断问题。
  - `directional_budget`（`DirectionalBudget.lean:381-386`）：
    - 假设：`(s : FiniteState) (f : Point -> Int) (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat)`。
    - 结论：`missCount s.toState (window L) (window L) (N - window L) <= (unique s.black).length + 2 * (L : Int) * (totalDefect (heights s.toState f L) (ceilBlocks N L) : Int)`。
    - 检查：当 `N < window L` 时 `N - window L = 0`，左端为 0，符合纸面对空区间的约定；另提供不含 `N - W` 且统计 `[0, N)` 的更强版本 `directional_budget_zero`（`DirectionalBudget.lean:348-358`）与 `directional_budget_floor`（`DirectionalBudget.lean:332-341`）。
    - 注：与 `BlackCountBound2.black_bound_finiteSupport` 不同，本文件未另行包装 `State + FiniteSupport` 版本，仅陈述在 `FiniteState` 上；但 `drafts/proof-status.md:697` 如实写作“对任意有限状态”，且可由 `BlackCountBound.finiteSupport_representation` 直接连接，不存在过度宣称。
  - `Sublinear` / `SublinearInt`（`DirectionalBudget.lean:399-405`）与 `sublinear_of_defect`（`DirectionalBudget.lean:441-450`）：对一切 `q > 0` 存在 `N0` 使 `∀ N ≥ N0, q * a N ≤ N`（及非负性）在非负序列上严格等价于 `a(N) / N → 0`（即 `o(N)`）。证明中 `sublinear_of_block_budget`（`DirectionalBudget.lean:407-421`）严格无漏洞。
  - 非空泛见证：`x_unitProjection`、`blank_budget_example` 及全称实例化 `blank_budget_all`（`DirectionalBudget.lean:452-472`）。
  - `drafts/proof-status.md:695-706` 叙述准确，未发现问题。

### 16. `PersistA/TimingCircuit.lean`

- **判定**：**无问题**
- **核查要点**：
  - `ClockWalk`、`walk_budget`、`circuit_budget`、`circuit_positive_voltage`、`return_segment_voltage_positive`、`two_gate_budget`（`PersistA/TimingCircuit.lean:13-62`）均为纯整数与归纳关系的精确算术引理，无截断减法，前提显然可满足（文件中未附实例）。
  - 备注：该模块目前未被 `PersistA/` 下其余模块导入（`FirstVisitCycle` 与 `TwoGateDecomposition` 直接展开算术），但作为独立基础组件与 `drafts/proof-status.md:629` 的描述相符。未发现问题。

### 17. `PersistA/TranslationShift.lean`

- **判定**：**无问题**
- **核查要点**：
  - `no_half_drift_table_symmetry`（`PersistA/TranslationShift.lean:39-108`）：假设 `ConsistentWord P w`、`0 < P`（冗余，无害）、`wordDrift P w = (2, -2)`，结论 `¬ DirectionTableTranslation.PreservesTables (2, -2) P w (1, -1)`。不依赖最小周期、顶层占满或增长量。
  - 非空泛性：文件内无见证定理，前提由 `stdHighwaySE`（`P = 104, drift = (2, -2)`）直接满足。
  - 与 `research/persist-A-width-2026-11-22.md:1591-1597, 1666-1673`（第 69、75 轮）及 `drafts/proof-status.md:628` 完全吻合，未发现问题。

### 18. `PersistA/GatePath.lean`

- **判定**：**无问题**
- **核查要点**：
  - `stable_gap_is_actual_closed_path`（`PersistA/GatePath.lean:5-23`）与 `two_short_closed_paths`（`PersistA/GatePath.lean:25-53`）用 `Drift.path_visit_of_stableTime` 构造携带跨周期进位的 `ContinuousPhasePath.ofStart`，证明物理位置同格闭合 `p.pos w len = p.pos w 0`（不虚构“首次返回”或“朝向闭合”）。`D0.toNat`、`D1.toNat` 均由 `0 < D0`、`0 < D1` 保护，无截断。
  - 下游由 `TwoGateDecomposition` 与 `GateRebase.stdHighwaySE_explicit_blocks` 实例化见证。与 `persist-A` 第 72 轮及 `drafts/proof-status.md:629` 一致，未发现问题。

### 19. `PersistA/TwoLaneCycle.lean`

- **判定**：**需修正（主要为 `drafts/proof-status.md:629` 表述不准；Lean 侧可选补充 `n = 4` 包装）**
- **Lean 代码核查**：
  - `Edge`（`PersistA/TwoLaneCycle.lean:7-9`）准确刻画 `(2, -2)` 双通道商图邻接关系：偶层步长 `±1` 且 `x mod 2` 翻转（`1 - a.2`），奇层步长 `±1` 且 `x mod 2` 不变。
  - `maximal_cycle_four`（`PersistA/TwoLaneCycle.lean:57-87`）在层坐标最高顶点 `q` 处证明 `next (next (next (next q))) = q`；`finite_reverse_cycle_four`（`PersistA/TwoLaneCycle.lean:127-140`）对有限单环 `Fin n` 证明 `∃ q, prevIndex^4 q = q`。
  - 逻辑说明：由于 `Edge` 每步改变层奇偶且 `two_step_lane`（`PersistA/TwoLaneCycle.lean:11-21`）使两步后 `c.2 = 1 - a.2 ≠ a.2`（在 `Int` 上 `2a.2 = 1` 无解），单环长度不能为 1、2、3，因此 `prevIndex^4 q = q` 数学上确实强制 `n = 4`。但本文件**未显式陈述 `n = 4`**（或四点两两互异），仅输出了四步回归等式（`research/persist-A-width-2026-11-22.md:1715` 曾如实记录此事）。
- **发现的问题（需修正）**：
  - **位置**：`drafts/proof-status.md:629`（对照 `PersistA/TwoLaneCycle.lean:57-63, 127-130`）。
  - **原文**：“双通道极大环长为 4（`TwoLaneCycle`）”
  - **具体问题**：
    1. **误译“maximal”**：`maximal_cycle_four` 中的 `maximal` 指的是在证明中取层坐标最高的顶点 `q`，而非“极大环”或“最大环长为 4”；数学事实是该双通道商图的**全部简单有向环**长度都恰为 4（`persist-A:1488`：“双通道商图的全部简单有向环均为四环”）。
    2. **与 Lean 陈述略有落差**：`TwoLaneCycle.lean` 的结论是 `next^4 q = q` / `prevIndex^4 q = q`（周期整除 4），尚未显式写出 `n = 4`。
  - **修改建议**：将 `drafts/proof-status.md:629` 改为“双通道商图简单有向环在最高层顶点处四步闭合（`TwoLaneCycle.maximal_cycle_four` / `finite_reverse_cycle_four`，结合 `Edge` 蕴含环长恰为 4）”；若希望接口自足，亦可在 `PersistA/TwoLaneCycle.lean` 为 `finite_reverse_cycle_four` 增加 `n = 4` 的 5 行推论。

### 20. `PersistA/FirstVisitMap.lean`

- **判定**：**无问题**
- **核查要点**：
  - `firstOf`（`PersistA/FirstVisitMap.lean:7-8`）与 `firstPred`（`PersistA/FirstVisitMap.lean:29-30`）准确定义类首访相位及首访前驱。
  - `firstPred_class_edge`（`PersistA/FirstVisitMap.lean:47-58`）与 `firstPred_clock`（`PersistA/FirstVisitMap.lean:60-76`）准确使用目标 `i` 的入向 `inDir w i`（未误用源相位 `firstPred i` 的出向）。
  - `zero_port_successor`（`PersistA/FirstVisitMap.lean:89-117`）严谨证明了当 `b` 秩零、`firstPred b = a` 且 `outDir w a = inDir w b` 时必有真实后继 `Drift.succ P a = b`。
  - 下游由 `FirstVisitCycle`、`TwoGateDecomposition` 与 `GateRebase.stdCore` 实例化。与 `persist-A` 第 76、80 轮一致，未发现问题。

### 21. `PersistA/FiniteOrbitCycle.lean`

- **判定**：**无问题**
- **核查要点**：
  - `exists_simple_cycle`（`PersistA/FiniteOrbitCycle.lean:32-81`）对任意在有限列表上封闭的函数，取最小正返回长度，构造单射 `c : Fin n → α` 满足 `f (c i) = c ((i + 1) mod n)`。证明严谨，无隐藏前提。未发现问题。

### 22. `PersistA/FirstVisitCycle.lean`

- **判定**：**无问题**
- **核查要点**：
  - `exists_rank_zero_cycle`（`PersistA/FirstVisitCycle.lean:9-26`）、`key_injective_on_rank_zero`（`PersistA/FirstVisitCycle.lean:31-41`）、`firstPred_edge`（`PersistA/FirstVisitCycle.lean:44-62`）、`exists_rank_zero_four_return`（`PersistA/FirstVisitCycle.lean:65-90`）、`four_clock_positive`（`PersistA/FirstVisitCycle.lean:105-131`）、`firstPred_four_directions`（`PersistA/FirstVisitCycle.lean:155-180`）与 `exists_core`（`PersistA/FirstVisitCycle.lean:205-224`）端到端连贯，忠实于 `persist-A` 第 77–81 轮。
  - 核查 `Core P w`（`PersistA/FirstVisitCycle.lean:183-203`）的非退化性：虽然未单列 `a0 ≠ a1` 等字段，但由 `dir0..dir3`（`a0, a1` 入向 `.south`，`b0, b1` 入向 `.east`）及 `edge0..edge3`（经一条 `.south` 边与一条 `.east` 边后，层复原而 `x mod 2` 翻转），自动保证 `a0, b1, a1, b0` 属于四个互异平移类，四相位必然两两不等，不存在 2 环退化。
  - 下游由 `GateRebase.stdCore`（`PersistA/GateRebase.lean:680-700`）显式见证非空泛。未发现问题。

### 23. `PersistA/TwoGateDecomposition.lean`（重点审查）

- **判定**：**无问题**
- **重点定理审查**：
  - `exists_two_gate_decomposition`（`PersistA/TwoGateDecomposition.lean:120-148`）：
    - 假设：`(hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2, -2))`——无最小周期、顶层占满、标准尾迹或增长量假设。
    - 结论：存在 `c : Core P w` 与 `d0, d1 : Nat`，满足 `0 < d0, 0 < d1, d0 < P, d1 < P, P = d0 + d1 + 4`，真实后继 `Drift.succ P c.b0 = c.a1`、`Drift.succ P c.b1 = c.a0`，且从 `c.a0` 出发长 `d0` 的连续提升路径 `p0` 终相位为 `Drift.pred P c.b0` 并回到同一物理格（`p0.pos w d0 = p0.pos w 0`），从 `c.a1` 出发长 `d1` 的连续提升路径 `p1` 终相位为 `Drift.pred P c.b1` 并回到同一物理格（`p1.pos w d1 = p1.pos w 0`）。
    - 桥步方向核对：`c : Core P w` 固定 `inDir c.b0 = inDir c.b1 = .east` 与 `inDir c.a0 = inDir c.a1 = .south`，再由同文件中的 `core_outgoing`（`PersistA/TwoGateDecomposition.lean:21-27`）与 `core_exit_data`（`PersistA/TwoGateDecomposition.lean:40-77`）确定退出方向为 `.east`、桥点出向为 `.south`，确为“同格闭合游程 C0 → E,S → 同格闭合游程 C1 → E,S”。
    - 注：证明未声称闭合游程为“首次”返回，也未给出横向高度界，与 `persist-A` 第 64、82 轮及 `drafts/proof-status.md:627, 631` 完全吻合。
    - 非空泛性：下游在 `PersistA/GateRebase.lean:665-706` 以标准字 `stdHighwaySE`（`d0 = 8, d1 = 92`）完整实例化。未发现问题。

### 24. `PersistA/SharedBoundary.lean`

- **判定**：**无问题**
- **核查要点**：
  - `onRay` / `onRay_iff`（`PersistA/SharedBoundary.lean:25-37`）精确刻画 `p + 2j(1, -1)`（`j ≥ 0`）；`Block.T_eq_finite_sum`（`PersistA/SharedBoundary.lean:201-207`）验证 `T` 确为该半线上访问重数之和模 2。
  - `Block.Legal`（`PersistA/SharedBoundary.lean:138-139`）经 `Block.legal_iff_reads`（`PersistA/SharedBoundary.lean:540-554`）证明与真实蚂蚁动力学 `LangtonsAnt.run` 逐位读色完全等价。
  - `consistentWord_iff_sharedBoundary`（`PersistA/SharedBoundary.lean:425-437`）与 `consistentWord_iff_exists_sharedBoundary`（`PersistA/SharedBoundary.lean:440-451`）建立完整双向等价，且仅在各块实际访问支撑 `Support` 上约束初始颜色，不附加未访问格条件；`boundary_replay`（`PersistA/SharedBoundary.lean:567-580`）与 `boundary_after_U`（`PersistA/SharedBoundary.lean:582-590`）进一步证实两块从同一棋盘连续执行、切点处不重置棋盘。
  - 非空泛见证：`stdHighwaySE_split_geometry`（`cut = 90`）与 `stdHighwaySE_nonvacuity`（`PersistA/SharedBoundary.lean:632-655`）。
  - `drafts/proof-status.md:633-640` 叙述忠实，未发现问题。

### 25. `PersistA/GateRebase.lean`（重点审查）

- **判定**：**无问题**
- **重点定理审查**：
  - `cyclicShift_consistent`（`PersistA/GateRebase.lean:17-26`）、`cyclicShift_pos`（`PersistA/GateRebase.lean:40-55`）与 `cyclicShift_drift`（`PersistA/GateRebase.lean:57-68`）正确处理循环移位引起的朝向旋转归一化：锚相位 `c.a0` 原入向为 `.south`，归一化为 `.north` 后整体旋转 180°，漂移由 `(2, -2)` 变为 `(-2, 2)`，切点位移由 `(1, -1)` 变为 `(-1, 1)`。
  - `Northwest` 命名空间（`PersistA/GateRebase.lean:268-567`）将第二块原点与前向射线同步旋转 180°（`Northwest.advance p k = (p.1 - k, p.2 + k)`），并独立重证完整充要判据 `Northwest.consistentWord_iff_sharedBoundary`（`PersistA/GateRebase.lean:534-545`）及 `Northwest.consistentWord_iff_exists_sharedBoundary`（`PersistA/GateRebase.lean:547-557`），无射线方向遗漏旋转的错误。
  - `GateBlocks`（`PersistA/GateRebase.lean:138-153`）及 `GateBlocks.second_color` / `GateBlocks.second_pos`（`PersistA/GateRebase.lean:570-591`）确认切点 `d0 + 2` 处两块精确对应两段闭合游程加各自两步桥，且第二块逐位、逐点等同于在 `c.a1` 独立重定基后的朝北轨迹。
  - `exists_gate_rebase_sharedBoundary`（`PersistA/GateRebase.lean:633-643`）：
    - 假设：`(hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2, -2))`。
    - 结论：构造 `c : Core P w` 与 `d0, d1`，同时证明 `GateBlocks P w c d0 d1`、`ConsistentWord P u`、两块以 `Northwest.initialU` / `Northwest.initialV` 各自 `Legal`（即满足真实蚂蚁执行），并满足 `Northwest.Boundary`。此处并非利用 `initialU`/`initialV` 定义制造的同义反复：真正的非平凡内容在于这两个特定棋盘同时使两块内部翻色合法（结合 `Block.legal_unique_on_support`，任何其他内部合法棋盘在访问支撑上必与之重合，因而同样满足 `Northwest.Boundary`）。
  - 非空泛见证：`stdHighwaySE_nonvacuity`、`stdCore`（`(16, 15, 26, 25)`）、`stdHighwaySE_explicit_blocks`（`d0 = 8, d1 = 92`，第二块确跨原周期 `103 → 0` 接缝）与 `stdHighwaySE_explicit_boundary`（`PersistA/GateRebase.lean:665-720`）。
  - `drafts/proof-status.md:640` 叙述准确，未发现问题。

---

## `drafts/proof-status.md` 专节汇总

除上述已归入对应模块节的 3 处“需修正”与 1 处“存疑”外，顺带记录 3 处非数学过度宣称的文档陈旧细节，供后续整理：

1. **需修正 — `drafts/proof-status.md:592`（`RootWord.lean` 推论）**：将“任意素数倍”写入目标 B 反例列表，误包含了标准公路对应的素数 `m = 2`；且称“任意奇数倍……都直接是目标 B 的反例，无需另加最小周期假设”，未区分 `m = 1` 与奇合数 `m` 须经取最小根才能保证周期最小。建议改写为限定奇素数 `m ≥ 3`（直接为最小周期反例）与奇数 `m ≥ 3`（取最小根后为最小周期反例），并注明等价改写为纸面推论。
2. **需修正 — `drafts/proof-status.md:618`（`WidthDefects.lean` 前提范围）**：写“**后两式需要 `botLayer ≤ t`**”，遗漏了紧邻前文同样显式要求 `botLayer P w ≤ t` 的 `runEdgeOccurrence_perm`（`WidthDefects.lean:1090`）。建议改为“以上三式均需要 `botLayer ≤ t`”。
3. **需修正 — `drafts/proof-status.md:629`（`PersistA/TwoLaneCycle.lean` 概括）**：写“双通道极大环长为 4”，误译了 `maximal_cycle_four` 中的 `maximal`（指层高最大顶点，而非极大环），且未区分 Lean 结论 `next^4 q = q` / `prevIndex^4 q = q` 与 `n = 4` 的最终包装。建议改为“双通道商图简单有向环在最高层顶点处四步闭合（`TwoLaneCycle`）”。
4. **存疑 — `drafts/proof-status.md:672`（`RootTail.lean` 简写）**：分号后的“若坐标 `x` 每 `P` 步前进 `m`、最终每 `q` 步前进 `u ≥ 0`，则 `m ≤ u`”省略了对前句 `LeastReadPeriod P w` 及 `q > 0` 条件的承接，单看可能被误解为仅靠坐标平移即可推出 `m ≤ u`。建议补充“在此同一 `P, q`（`q > 0`）前提下”。
5. **文档陈旧附注（非过度宣称）**：
   - `drafts/proof-status.md:3` 顶部更新日期仍为 `2026-11-22`；
   - `drafts/proof-status.md:566-568` 标题仍标注“部分 / 一般定理未完成”，但紧随的 `L571` 已由 `DiagonalWinding.lean` 补齐；
   - `drafts/proof-status.md:604` 仍写“第 36 轮的完整切口求和式、第 33–35 轮的游程与缺陷计数仍未形式化”，但紧随的 `L606`、`L614` 已完成形式化。
