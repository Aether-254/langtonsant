# 第二轮 brainstorm：任务书（2026-11-22 晚）

本文件是任务定义，不是结果。每个题目由一个 GPT-6 Astra 会话独立完成，结果写入各自指定的新文件。

## 当前已证明的基线（纯内核，均已提交）

- 单位对角完整漂移 `(±1,±1)` 不可能：`UnitDiagonal.no_unit_diagonal_periodic_tail'`。
- 一般漂移稳定秩工具：`DriftRank.lean`（`LangtonsAnt.Drift.*`：`SameClass`、`lift`/`base`、`stableTime`、`priorPhases` 长度即类内秩、首次返回秩加一 `path_firstReturn_rank`、固定源类与方向的保序匹配，平移常数 `1 − P·liftStep v c d`）。
- 增长量：`PeriodicGrowthResidue.lean`（`wordGrowth` = 奇重数完整平移类数；`g = #R − #L` = 每周期黑格净增；`4 ∣ g`；`g ≥ 2·max(|a|,|b|)`；`g = 4` 时漂移只能是单位对角、两格轴向、两格对角；标准 104 字 `g = 12`）。
- 两格对角 `(2,−2)`：`TwoCellDiagonalExtremal.lean`（极值线刚性、双通道流量、`K` 偶）。`TwoCellAxial`、`TwoCellDiagonal`（`g ≥ 8` 的剩余部分）正由其他代理完成。
- 列表逆序工具：`PortInversion.lean`。
- 记录对：`RecordPair.lean`（`100001`、`4|v|₁ ≤ P`）；`RecordSupport.lean`（记录黑读为第二次访问、同前沿支撑区间分离）；`RecordSupportExamples.lean`（跨前沿交错、通用来源链接不成立的反例）。
- 小周期：纯内核 `P ≤ 13`，`native_decide` `P ≤ 37`。

必读背景：`drafts/proof-status.md`；`research/dual-front-results-2026-11-22.md`（上一轮结论：缺口是来源链接 `C_k ~ A_{k+1}`，即沿前沿净滑移为零；跨类合并保序已被标准字反例否定）；`research/drift-next-steps-2026-11-22.md`；`research/drift-ke-source-audit-2026-11-22.md`；`research/growth-blueprint-2026-11-22.md`；`research/open-blocks-survey.md`。

## 通用规则（propose → refute → verify）

只接受以下之一：(1) 完整纸面证明，附精确量词、全部假设、与 Jillhewar/Ke 已知结果的区别，以及一个可在 Lean 中先实现的最小引理；(2) 满足全部自洽条件的明确反例；(3) 准确定位失败的推理步骤。必须自我对抗检验：标准字的任意幂与旋转、跨周期提升量、合法首次返回的相邻秩、局部振荡子、仅满足 incidence 条件的伪轨迹、`RecordSupportExamples` 的反例。单纯增加周期下界、重复已知结论、把局部无解当全局分类，均不算完成。

只读；只新建指定的结果文件（正式简体中文）。可在仓库外临时目录做小规模 Lean/Python 实验并在结束时删除；实验不能替代证明。不得修改已有文件、不得提交、不得 `lake build` 重目标、不得自行开子代理。

## 题目

**T1 来源链接 / 零净滑移**（结果：`research/brainstorm2-T1-source-link-2026-11-22.md`）。对白背景自洽周期字，证明或否定上一轮的候选命题 `B`：相邻记录对满足 `C_k = A_{k+1}`；或其弱化——一个完整周期内沿前沿滑移 `η_k` 的净和为零。重点利用首读为白、黑读来源、同前沿支撑分离与 `DriftRank` 的类内工具；明确区分只对周期尾成立与对一般暂态成立的命题。

**T2 对角倍数 `(m,−m)`，`m ≥ 2`**（结果：`research/brainstorm2-T2-diagonal-multiples-2026-11-22.md`）。单位对角论证在 `m > 1` 时于“E,S 两步留在同一类”处失效（每层 `m` 个余数类，`liftStep` 依赖类）。在**最小正周期**假设下（否则标准字的重复即反例），研究：(a) 能否排除 `m ≥ 3`；(b) 能否把 `m = 2` 的字限制到有限族。要求明确周期最小性、本原方向与完整位移中最大公约数三者的区别。

**T3 宽度控制：漂移 `(±2,±2)` 是否迫使标准字**（结果：`research/brainstorm2-T3-width-2026-11-22.md`）。Jillhewar 只在计算上排除了对角宽度 ≤ 8；Ke 的周期上界依赖已知尾迹。寻找一个与未知轨道无关、能约束横向宽度 `W` 或尾迹大小的机制（例如利用 `g` 的上界、极值线刚性、双通道流量），或给出说明这类机制不存在的伪轨迹/反例结构。

**T4 第一开放块：有限初态的最终周期性**（结果：`research/brainstorm2-T4-periodic-tail-2026-11-22.md`）。不要求解决。任务是给出一个**可检验的中间命题**：它严格弱于 `PeriodicTail`、但非平凡，并且有希望被证明或被反驳（例如对某类初态族、或在附加可验证条件下的最终周期性）；同时说明现有势函数/时钟路线的精确边界（参见 `research/drift-next-steps-2026-11-22.md` 第 5 节）。
