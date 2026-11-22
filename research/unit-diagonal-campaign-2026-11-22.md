# 单位对角完整漂移排除：形式化战役进度

日期：2026-11-22。分支：`single-black-cell`。目标：在纯 Lean 内核中（不使用 `sorry`、`axiom`、`native_decide`）形式化 Ke 的定理 `ud:thm:unit`——有限支撑初态的任意正周期尾，其完整单周期位移不能为 `(±1, ±1)`。

## 已完成的准备

- 数学蓝图（32 项引理 DAG，纸面审阅未发现实质缺口）：[unit-diagonal-math-blueprint-2026-11-22.md](unit-diagonal-math-blueprint-2026-11-22.md)。
- 仓库映射与接口设计：[unit-diagonal-repo-map-2026-11-22.md](unit-diagonal-repo-map-2026-11-22.md)。要点：漂移为 `(1,-1)` 时 `(priorPhases P w i).length` 即稳定秩；核心定理落在 `ConsistentWord` 层面，轨道版本经循环移位与旋转归约。
- 两份文件独立给出一致结论：`weight` 最大层唯一事件为东入、白读右转、南出。

## 模块划分（各模块独立文件，尚未加入 `lakefile.toml`）

| 文件 | 内容 | 对应引理 | 状态 |
| :--- | :--- | :--- | :--- |
| `UnitDiagonalInterleave.lean` | 二元交错引理（与蚂蚁无关）`UnitDiagonal.interleave_bridge` | L28 | 完成；独立复核：`-M1536 -DwarningAsError=true` 编译通过，公理仅 `propext`、`Classical.choice`、`Quot.sound` |
| `UnitDiagonalPorts.lean` | 固定方向字几何证书（`walk_east_south`、五个 `firstReturn_*`）；抽象端口计数式 `even_layer`、`odd_layer` | L10、L15 | 完成；独立复核：编译通过，公理仅 `propext`、`Quot.sound` |
| `UnitDiagonalReduction.lean` | 以 `CoreUnitSE` 为假设的旋转/循环移位归约外壳：`no_unit_diagonal_periodic_tail`（轨道形式）、`consistentWord_not_unitDiagonal`（字形式） | L01、L31、L32 | 完成；独立复核：编译通过，公理仅三标准公理，`CoreUnitSE` 为显式假设，`HighwayFrom`/`ConsistentWord`/`wordDrift` 均为仓库原定义 |
| `UnitDiagonalRank.lean` | 稳定时间、稳定秩（= `priorPhases` 长度）、`ContinuousPhasePath`、键差公式、`firstReturn_rank` | L03–L06（不含秩满射）、L11、L13 | 完成；独立复核：编译通过，公理仅三标准公理 |
| `UnitDiagonalWords.lean` | 抽象层字引理 | L17、L18、L21–L23 | 完成；独立复核：编译通过，公理仅三标准公理；长度 ≤ 12 穷举检验无反例，`c = 2` 分支为空 |
| `UnitDiagonalMatching.lean` | 秩枚举双射；有向端口保序匹配 | L04 余项、L12 | 完成；独立复核：编译通过，公理仅三标准公理（`successor_stableTime` 含接缝；`successor_rank_order`；`ordered_bijection_position` 为通用引理） |
| `UnitDiagonalExtremal.lean` | 层步长与轴奇偶；极值层唯一 R 事件；宽度偶且为正；逐相位端口恒等式 | L07–L09、L14 | 完成；独立复核：编译通过（850 行），公理仅三标准公理；`topLayer_unique_phase`、`beta_eq_xor` 签名已核对 |
| `UnitDiagonalCore.lean` | 按秩的端口字、割边计数、`layerWidth_ge_four`、`first_inner_events`、`four_step_return_rank`、`second_inner_two_words`（A 层字为 `1000`，B 层字为 W8 或 W9） | L16–L22 | 完成（codex_2 Astra 于额度耗尽前完成至此）；独立复核：763 行编译通过，公理仅三标准公理；此文件冻结 |
| `UnitDiagonalInner.lean`、`UnitDiagonal.lean` | 第三内层、交错矛盾、`coreUnitSE`、无条件主定理 | L23–L27、L29–L30 | 完成（Gemini 4 Neon 接力）；独立复核见下 |

## 结论（2026-11-22 18:0x）

**主定理已在纯 Lean 内核中证明**：`UnitDiagonal.coreUnitSE`、`UnitDiagonal.no_unit_diagonal_periodic_tail'`、`UnitDiagonal.consistentWord_not_unitDiagonal'`。

独立复核：在空目录中按依赖顺序从零编译全部十个模块（`-M1536 -DwarningAsError=true`，零输出）；扫描 `sorry`/`axiom`/`native_decide`/`implemented_by`/`extern`/`unsafe`/`opaque`/`macro`/`elab`/`set_option` 等，仅命中注释；核对 `HighwayFrom`、`FiniteSupport`、`ConsistentWord`、`wordDrift` 均声明于仓库原有模块；三条主定理公理仅 `propext`、`Classical.choice`、`Quot.sound`。十个模块已加入 `lakefile.toml` 的 `PeriodicWords.roots`，`lake build UnitDiagonal` 通过；审计脚本 `scripts/UnitDiagonalChecks.lean`；`drafts/proof-status.md` 已增补条目。

分工记录：数学蓝图与 L03–L06、L11–L13、L12、L16–L22 由 GPT-6 Astra（codex_2）完成；仓库映射、L07–L09、L14 与 L23–L30 由 Gemini 4 Neon 完成；L10、L15、L17–L23 数据、L28 与归约外壳由 ECNU Max（DeepSeek V4.1 Flash）完成；Claude 负责编排、逐模块独立复核与集成。

待办：由另一模型做一次独立交叉审阅（`codex` 于 19:19 重置）；尚未提交。

`CoreUnitSE` 在归约外壳中仅作为显式假设出现，不是公理；在其被证明之前，不得宣称主定理已经形式化。

## 集成注意事项

- `LangtonsAnt.outDir`/`inDir`（Extremal）与 `LangtonsAnt.UnitDiagonalMatching.outDir`/`inDir`（Matching）定义相同但名称不同；联合导入已测试可编译，后续文件不要同时 `open` 两个命名空间，需要时补 `rfl` 桥接引理。
- `UnitDiagonal.beta`（Ports，列表函数）与 `LangtonsAnt.beta`（Extremal，逐相位布尔值）是不同对象。
- `topLayer` 以 `foldl max 0` 定义，依赖相位 0 位于层 0；在 `P = 0` 时无意义，但 `ConsistentWord` 已排除该情形。

## 集成规则

- 新模块只导入 `RecordPair`（或更少），不得导入 `PeriodicWordSmall`、`PeriodicWordCheck*`、`PeriodicWordFast`、`PeriodicNative.*`。
- 单文件检查：`& 'D:\langtonsant\tools\lean-4.36.0-windows\bin\lake.exe' env lean -M1536 -DwarningAsError=true <文件>`。
- 全部模块通过并完成 `#print axioms` 审计后，再统一加入 `PeriodicWords.roots`。
