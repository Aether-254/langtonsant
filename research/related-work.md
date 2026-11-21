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

### 1.3 Research Square rs-10516269（只核对到标题，正文未读）

- 标题：*Finite-Support Periodic Highways of Langton's Ant: Necessary Conditions, Transverse Exclusions, and Exact Search*，<https://www.researchsquare.com/article/rs-10516269>。
- 页面由 JavaScript 渲染。API 返回 403，Europe PMC 返回 503，作者、日期、摘要都没有取到。
- 从标题看，它很可能与本仓库的周期尾部归约、小周期排除以及 SAT 探索重叠。**在读到正文之前，不能声称本仓库“周期 ≤ 33 不存在周期尾部”的结论是新的。** 需要人工打开页面核对：
  1. 排除了哪些周期与漂移；
  2. “exact search” 覆盖的范围；
  3. 是否有形式化验证。

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
- 没有找到白背景周期轨道的分类或唯一性定理。rs-10516269 的正文未读，此结论待定。
- 除无界性之外，没有找到关于有限构形弹道逃逸的结果。
- 形式化方面，没有找到 Ke 以外的 Lean、Coq 或 Isabelle 工作。AFP、Lean Zulip、Agda、HOL4、ACL2、Metamath 没有单独检索，也没有单独检索 Codeberg、GitLab、HAL、OpenReview、SSRN。
