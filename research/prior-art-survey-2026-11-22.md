# 已有工作查重（2026-11-22）

由全网检索代理（GitHub、GitLab、Codeberg、SourceHut、Gitee；arXiv、HAL、Zenodo、Crossref、OpenAlex）汇总，未逐项人工复核原文；标注“需浏览器”的来源尚未读取。所有结论以原始来源为准。

## 一、与本仓库已形式化结果重合的已有工作

- **Ke，`kehao95/langtons-ant-core` @ `b3429c25`**（11 篇文章，Zenodo DOI 见其 `PREPRINTS.md`）。`wake_synthesis/proof/periodic-growth-closure.md` 的 Theorem A–C（`g ∈ 4ℤ`、`g ≥ 2·max(|a|,|b|)`、`g ≥ 8`；两格轴向 `P ≡ 4 (mod 8)`、`8 ∣ g`；两格对角奇偶混合）为纸面证明，归属 Jillhewar，未见 Lean 形式化——与本仓库 `PeriodicGrowth*`、`TwoCell*` 完全对应。单位对角排除亦属 Ke。
- **Jillhewar，`Atharva12456/langtons-ant-highway` @ `76a7e234`**；Research Square 预印本 `10.21203/rs.3.rs-10516269/v1`；Zenodo 补充材料 `10.5281/zenodo.21381637`。有限字可实现判据（对应本仓库 `PeriodicWordRealization`）；周期 ≤ 48 无公路（Java 穷举）；对角宽度 2 不可能、宽度 4 计算机辅助排除；研究笔记声称宽度 6、8 亦经计算机排除（因此对角宽度 ≥ 10）。
- **单黑格进入公路**：Ke 的 `one_black/`（Lean，含 `native_decide`）；imfinn `langton-two-black` @ `95e896e3`（Lean 4.30，至多两个黑格，61 个 `native_decide` 公理）。本仓库的单黑格证明为纯内核，信任基础不同。
- **小周期排除**：CrazyDubya/projects PR #17（合并 `d5b12400`，CaDiCaL）：偶数 `P ≤ 50`、`|d|₁ ≤ 6` 无公路；偶数 `P ≤ 104`、9×9 盒内只有经典公路。存在未解决的审查意见指出部分漂移可能被跳过，完备性未确立。与本仓库远端 SAT 有界盒扫描基本重叠。
- **未在他处见到**：`100001` 循环因子与 `4|v|₁ ≤ P`（`RecordPair.lean`）。

## 二、与开放题目 T1–T4 相关的已有结果（均未解决对应题目）

- **T1（来源链接 / 零净滑移）**：未见任何等价陈述。最接近的是 Ke `memory_feedback/` 的 crossing records（Hennie 交叉序列的改编）与轴向尾迹奇偶条件。
- **T2（对角倍数 `(m,−m)`）**：无排除结果。可用工具：Ke 的 `P ≤ g·(3^{W/2} − 1)`、`P² ≤ A₊A₋/κ²`、二次型奇偶筛选；结合 `g ≥ 2m`，固定 `W` 与 `g` 时 `m = 2` 有限。
- **T3（宽度控制）**：部分结果。Ke 的 thin-wake rigidity：漂移 `(2,−2)`、`g = 12`、`W = 10`、每个内部层至多一个奇类 ⇒ `P = 104` 且为标准字；W = 10 的矩不等式 `K = 2Σ(−1)^j (j−5)^2 o_j ≥ 168`，等号仅标准字；标准尾迹唯一性（给定标准 12 类尾迹，与周期无关，用 `P ≤ 168` 及 `P ≡ 8 (mod 16)`）。`W = 10` 且 `g` 任意、以及 `W > 10` 仍开放。
- **T4（最终周期性）**：只有条件结果与密度结果。Ke `factor_language/`：若未来所有 10-转向窗口都出现在标准字中则最终周期（最小周期 104、28 或 24）；`m` 个初始黑格时在 `12m + 212` 步内进入公路；区间不等式 `3(t−s) − 26(|B_t| − |B_s|) ≤ 351·N₁₀ + 322` 及其密度推论。Ke `memory_feedback/`：永不最终平移的轨道，其整段前缀的斜向宽度至少 `(1 − o(1))·log₂log T`。Ke 的 `NEXT_QUESTIONS.md`（2026-10-30）明确保留全部轨道最终周期性为开放问题。

## 三、其他相关条目

Gathellier：Zenodo `10.5281/zenodo.24224324`（公路的 22 个登入相位；公路开始前最后读取的格此后不再被读取）、`10.5281/zenodo.23643413`（扰动吸收，主要为经验结果）；Kersh 实心条与窄矩形进入公路（计算机辅助，`d3cc5c65`）；Etse，arXiv:2606.26677（有限区域的逃逸时间界）；gotrevor formal-conjectures 草稿 PR（仅为猜想的 Lean 陈述）；广义蚂蚁的非对角公路（Lutfalla 等，arXiv:2505.05426、2506.10482、2409.10124）提示证明必须使用 RL 规则的特有结构。未发现 Coq、Isabelle、Agda、ACL2 的形式化。

## 四、尚未读取（需浏览器或被拒）

Zenodo 记录页与 API（403）；Research Square 全文；Codeberg、Gitee 搜索；Google Scholar、Semantic Scholar、OpenReview 未直接查询；ScienceDirect S0167642320300812（2020 年的 Lean 有界网格元胞自动机论文，据摘要含 `ant.lean`，未核实）。

## 五、对本仓库的含义

1. 增长量与两格结论的贡献在于 **Lean 纯内核形式化**，数学归属 Jillhewar 与 Ke，`drafts/proof-status.md` 已据此标注。
2. 远端 SAT 有界盒扫描与 CrazyDubya 的目录大幅重叠，且有界盒结论本身不构成证明，宜降低优先级。
3. T3 方向应以 Ke 的 thin-wake rigidity 与 `W = 10` 矩不等式为起点，目标是 `W > 10` 的排除，避免重复已有结论。
