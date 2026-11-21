# 相关工作核对（2026-11-22）

本文件由一个 Sonnet 子代理检索预印本平台和代码平台后整理，其中关键条目由主线程另行打开原页面核对。每一条都注明了核对程度。“已核对”指读到了来源页面上的原文陈述，不含正文中的证明细节。

## 1. 与本仓库直接重叠

### 1.1 Hao Ke：单黑格定理（已核对页面陈述）

- 预印本 *Every One-Black-Cell Langton Ant Reaches the Period-104 Highway: A Lean-Checked Proof*，2026-10-26，版本 0.2.1，CC BY 4.0。
  - 页面：<https://www.kehao.me/papers/langtons-ant-one-black/>
  - 代码：<https://github.com/kehao95/langtons-ant-core>（`one_black/`）
  - DOI：README 记为 10.5281/zenodo.23844645，论文页记为 10.5281/zenodo.23675960，二者未对齐。
- 陈述：恰有一个黑格的有限状态，在任意位置、任意朝向下，都会出现完整的标准 P104 轨迹（允许平移与四分之一转）。这与本仓库的 `singleBlackAt_standard` 在数学上是同一结论。
- 方法（页面原文）：“The infinite reductions, geometric guards and certificate-soundness theorems are formalized in Lean 4, with three finite reports evaluated using native_decide.” README 写明复现需要 Lean 4.30.0。
- **与本仓库的关系**：
  - 该结论在我们之前已有人发布，我们的结果应表述为独立的第二个形式化证明，并引用该工作。
  - 已知的区别在信任基础：本仓库 `singleBlackAt_standard` 的公理审计只有 `propext`、`Classical.choice`、`Quot.sound`，全程用 `decide +kernel`，没有 `native_decide`；Ke 的证明有三处 `native_decide`。
  - 证明路线是否同构尚未比较。Ke 把问题归约为 22 个仿射前沿通道，其中 21 个靠几何分离处理，1 个需要单独的碰撞时间论证；本仓库按首访相位分为 22 个情形，其中相位 49 单独处理。两边都出现 22 个情形，值得逐一对照。

### 1.2 同一仓库的其他结果（只读了 README 陈述）

- **Wake rigidity**：“P104 uniquely minimizes the signed quadratic odd-wake moment at full drift (2,-2) and width ten.” 这是某个特定泛函的唯一极小性，不是“白背景自洽周期轨道唯一”。因此它不覆盖 `ConsistentWordsAreStandard`。
- **Clock and escape**：正方形区域的逃逸时间上界为 `(13·3^(n−1)−2n²−4n−5)/2`；固定高度矩形的阶为 `⌊H/2⌋+1`。
- **Four and five rows**：四行的精确最大值为 `34n−150`。
- README 说明其 `research/` 笔记不是已发表的定理。

### 1.3 Jillhewar：有限支撑周期公路（已通读全文）

- A. Jillhewar，*Finite-Support Periodic Highways of Langton's Ant: Necessary Conditions, Transverse Exclusions, and Exact Search*，Research Square 预印本 rs-10516269，正文日期 2026-07-21，发布日期 2026-07-30，CC BY 4.0。
  - DOI：10.21203/rs.3.rs-10516269/v1。
  - 代码与数据：Zenodo 10.5281/zenodo.21381637，镜像 <https://github.com/Atharva12456/langtons-ant-highway>。
- 主要结果（均以“有限支撑、最终周期、漂移非零”为前提）：
  - **Thm 3.1 周期可实现判据**：给出“无限周期字是有限支撑轨道的迹”的充要条件，并构造显式种子。它与本仓库的 `ConsistentWord` / `periodic_tail_consistent_at_start` 对应。差别在于，他们允许种子含黑格（稳定字以 R 开头即可），本仓库则把问题归约到白背景自洽字。
  - **Thm 6.1、Cor 6.5、Thm 7.1、Cor 7.3**：
    - 每周期的黑格净增长 `g = #R − #L` 属于 `4ℤ_{>0}`，并且 `g ≥ 2·max(|a|,|b|)`；
    - 不存在零增长的“干净平移子”，他们给出了两个独立证明。
    - 本仓库调研 §3.3 的转向平衡恒等式只是其中的弱形式。
  - **Thm 9.1 极值线刚性**（对角漂移）：两条极值层线上的转向都是 R，其中每个格子恰被访问一次，横向宽度 W 为偶数。这与本仓库调研 §3.2 的“侧向极值层”本质相同；§3.2 声称适用于一般的 `a·b ≠ 0`，二者之间的差别尚未核对。
  - **Thm 9.3、9.5**：对角漂移下，任何周期都不可能有横向宽度 2 或 4，因此 W ≥ 6。宽度 4 的证明依赖计算机辅助的“空白列”枚举（Lemma 9.4，12 条边）：由两套独立程序复现，Lean 只检查了秩递减这一部分，枚举的完备性不在 Lean 范围内。Remark 9.6 指出，同样的单列论证在宽度 6 处失效（存在局部振荡子）。
  - **Thm 10.1**：不存在周期 ≤ 48 的有限支撑周期公路。方法是 Java 穷举，在不依赖 Thm 7.1 的变体上逐个评估判据；长度 ≤ 18 的部分另有 Python 暴力复现。这一结果**没有在 Lean 中形式化**。论文明确写明周期 50 至 102 不在其覆盖范围内。
  - **Lean 部分**：Lean 4.32.0，仅用标准库，不用 `native_decide`，只检查了选定的代数核。原文：“What remains outside Lean is the extraction of that word and of the local geometric charge certificates from an arbitrary periodic ant orbit... neither it nor Conjecture 1.1 is asserted as an unconditional Lean theorem.”
  - **Problem 11.1 / 11.2**：有界活动核心（对应本仓库的“周期尾部”这一块）与周期分类（对应 `ConsistentWordsAreStandard`）。这两个问题与本仓库的两个开放块一一对应。
- **与本仓库的关系**：
  - 在结论范围上，他们走得更远：周期下界为 48（本仓库为 33），还有对所有周期都成立的宽度 2 与宽度 4 排除。本仓库此前在调研文档中称“周期 ≤ 33 的结论可能是新的”，这一说法已撤回。
  - 本仓库的不同之处在于**端到端的形式化**：
    - 归约 `HighwayConjecture ↔ (∀ 有限 s, PeriodicTail s) ∧ ConsistentWordsAreStandard`，以及从任意有限支撑轨道到自洽字的提取，均为纯内核证明；
    - 小周期排除由 Lean 检查，其中 ≤ 13 为纯内核，≤ 33 使用 `native_decide`。
    - 他们恰好把“从轨道到字的提取”放在了 Lean 之外。
  - 可以做的非重复工作：
    1. 在本仓库框架内端到端形式化他们的 Thm 9.1、9.3、9.5，包括 Lemma 9.4 枚举的完备性，从而得到“对角漂移下宽度 ≤ 4 的周期尾部不存在”的完整 Lean 定理；
    2. 把 Lean 认证的周期下界继续往 48 推进；
    3. 处理周期 50 至 102，例如本仓库在受限盒内做的 SAT 探索。
  - 本仓库调研 §3.1 的“前沿记录对”（因子 `100001`，以及 `P ≥ 4·|v|₁`）在该文中没有出现。该文的 Prop 4.3 讨论的是原轨道相对初始支撑包围盒的记录，不是同一个陈述。

## 2. 其他相关工作

- **Etse，*How Long Can the Escaping Ant Be Confined?***，arXiv 2606.26677（2026-06-25，已核对摘要）。研究蚂蚁在有限连通区域内停留的最长时间：正方形区域为阶乘级，高度 2、3 的矩形为线性。它不涉及周期轨道。另有一篇 MFCS 2026（LIPIcs vol. 386）论文的主题相同，PDF 未能提取正文。
- **Vaidyanathan**，<https://github.com/VishnuVaidyanathan/langtons-ant-census>（MIT，已核对仓库页）。
  - 结论：对 K ≥ 4，空白网格上的 L^(K−1)R 广义蚂蚁从第 24K−17 步起处于周期 16K−12 的公路。证明是 12735 行证书，由 Python 独立检查，不是 Lean。
  - 另有 4015 台机器各跑 100 万步的普查数据。对象是广义蚂蚁，但“符号化颜色 + 证书”的方法可以参考。
- **GitHub PR**：<https://github.com/elder-plinius/V3R1T4S/pull/613>（已核对 PR 页）。
  - 蚂蚁位于 (0,0)、朝北，对 6×6 盒内全部 2^36 个初始图案做模拟，声称都进入 P104 公路，最大暂态为 375545 步。
  - 属于实验，不是证明，只覆盖一个蚂蚁位置；原始输出没有保留。可以作为少黑格配置的交叉验证数据。
- **OEIS A255938**（已核对页面）：空白网格上走 n 步后的黑格数，并记有 `a(n+104) = a(n) + 12`（n > 9976）。
- **Lutfalla，arXiv 2506.10482**（LLLR 广义蚂蚁，只读了摘要）；**Tokarz，arXiv 1807.08789**（周期性直行变体，只读了摘要）。二者与经典规则的弱相关。

## 3. 未找到

- 除 Ke 之外，没有找到经典 RL 蚂蚁公路猜想（或其特例）的其他证明或声称的证明。
- 没有找到白背景周期轨道的分类或唯一性定理。Jillhewar 的论文给出了许多必要条件与有界排除，但同样没有给出分类（见 1.3）。
- 除无界性之外，没有找到关于有限构形弹道逃逸的结果。
- 形式化方面，没有找到 Ke 以外的 Lean、Coq 或 Isabelle 工作。AFP、Lean Zulip、Agda、HOL4、ACL2、Metamath 没有单独检索，也没有单独检索 Codeberg、GitLab、HAL、OpenReview、SSRN。
