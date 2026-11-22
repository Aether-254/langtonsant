# 研究任务书：双记录前沿的时序障碍（非对角漂移）

日期：2026-11-22。执行者：GPT-6 Astra（`codex`，`reasoningEffort` 取最高可用档）。本文件是任务定义，不是结果。

## 背景

- 已在纯内核中证明：单位对角完整漂移 `(±1, ±1)` 不可能（`UnitDiagonal.no_unit_diagonal_periodic_tail'`）。证明工具为稳定时间 `τ_i = i − P·lift_i`、首次物理返回使稳定秩恰好加一（`firstReturn_rank`）、有向端口按稳定时间保序匹配（`UnitDiagonalMatching`）。
- 一般漂移版本的同类工具已完成并通过独立复核：`DriftRank.lean`（命名空间 `LangtonsAnt.Drift`；纯内核）。要点：`SameClass v p q := ∃ z, q = p + z•v`；`lift`、`base` 规范分解；`Drift.mem_priorPhases_iff_stableTime`（任意 `v ≠ 0`，`priorPhases` 的长度即完整平移类内的稳定秩）；`path_firstReturn_rank`（首次物理返回使秩加一）；`successor_stableTime_of_class`（固定源类与方向时稳定时间平移常数 `1 − P·liftStep v c d`）；`departure_rank_position_eq_arrival_rank_position`（保序匹配）；`standard_word_nonvacuous`（标准 104 字满足前提）。注意 `LangtonsAnt.Drift.*` 与单位对角模块有同名声明，引用时写全限定名。
- 已有：`RecordPair.lean` 的 `100001` 记录对、`4|v|₁ ≤ P`；`RecordSupport.lean` 的记录黑读恰为第二次访问、同前沿支撑区间严格分离；`RecordSupportExamples.lean` 的反例（跨前沿区间可交错、通用来源链接不成立）；`AxisClockObstruction.lean`。参见 `research/brainstorm-results-2026-11-22.md` 与 `research/drift-next-steps-2026-11-22.md` 第 4、6 节。

## 问题

对漂移 `v = (a, b)` 且 `a² ≠ b²`（含轴向非零漂移），两个线性形式 `F₊ = sign(a+b)(x+y)` 与 `F₋ = sign(a−b)(x−y)` 每周期都严格增长，因此有两套记录前沿，各自给出 `100001` gadget。问：保留 gadget 的精确位置、首次回返与黑读来源，并结合稳定秩相邻与保序匹配，能否对所有正周期 `P` 推出矛盾（即排除全部非对角完整漂移），或至少排除轴向漂移？

## 交付要求（propose → refute → verify）

只接受以下三种结果之一：
1. 完整的纸面证明，附精确量词、全部假设、与 Jillhewar/Ke 已知结果的区别，以及一个可在 Lean 中先实现的最小引理；
2. 满足全部自洽条件的明确反例或伪轨迹，说明哪条候选推理失败；
3. 准确定位推广失败的那一步。

必须自我对抗检验：标准字的任意幂与旋转、跨周期提升量、合法首次回返的相邻秩、已知局部振荡子、仅满足 incidence 条件但不可实现的伪轨迹、`RecordSupportExamples` 的反例。单纯增加周期下界、重复 `g ≥ 8`、把局部无解当作全局分类，均不算完成。

## 约束

只读，外加一个新文件 `research/dual-front-results-2026-11-22.md`（正式简体中文）。可在临时目录用 Lean 或 Python 做小规模实验，但不得修改仓库已有文件、不得提交、不得 `lake build` 重目标。实验结果不能替代证明。
