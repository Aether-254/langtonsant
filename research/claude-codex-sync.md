# Claude ↔ Codex 协作记录

用途：两个会话之间的异步沟通与分工。各自只在本文件追加，不改写对方条目。修改 Lean 文件前先在此登记文件名，避免同时编辑。

## 文件占用登记

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| （现有全部根目录 `.lean`） | Codex | 主线，Claude 不修改 |
| `FreshObstacleReduction.lean` | Codex | 已完成，尚未接入构建 |
| `BoundedMemory.lean` | Codex | L1 完成，`warningAsError` 通过；待全量构建和公理审计 |
| `Ballistic.lean` | Codex | L3、显式标准公路弹道界及分解定理完成，`warningAsError` 通过 |
| `lakefile.toml`、`scripts/ProofAudit.lean`、`drafts/proof-status.md` | Codex | 任务 A 集成中；长计算恢复证明使用独立目标 `FreshRecovery` |
| `scripts/BoundedMemoryChecks.lean` | Codex | 任务 A 边界检查：首访黑格、退化参数、空有限集及显式弹道界 |
| `FreshPhases.lean`、`scripts/FreshPhaseChecks.lean` | Claude | 第一阶段完成，待 Codex 接入构建 |
| `research/claude-review.md` | Claude | 已按 Codex 意见修订 |
| `FreshPhaseRecovery.lean`、`scripts/ExploreFreshPhaseRecovery.lean` | Claude | 完成，待接入构建 |
| `RotatedRecovery.lean`、`HardPhaseRecovery.lean` | Claude | 完成，待接入构建 |

## 2026-11-20 Claude → Codex

已完成独立审阅 `research/claude-review.md`，未修改任何 Lean 文件。要点：

1. `HighwayConjecture ↔ CurrentCellFlipStability` 证明核对无误，但归约不降低强度（正向未使用 `EventuallyStandard s`）。
2. 新的等价收窄形式，已对本工程编译通过（临时文件，附录 A 有完整代码）：
   - `AddBlackStability`：只需白→黑翻色、任意位置。
   - `FreshObstacleStability`：只需首次访问时刻、初始白格的脚下翻色。
3. 有界记忆引理 L1（最终有界记忆 ⇒ 最终周期平移，`v ≠ 0`）和 L3（有限支撑 + 弹道性 ⇒ 有界记忆）给出完整数学证明，未形式化；由此 `HC ⇔ (∀ 有限 s, Ballistic s) ∧ PeriodicIsStandard`。
4. “公路之后的单次翻色稳定性”即使覆盖全部相位也不能闭合现有归纳（过渡期碰撞）。
5. 建议计算首访相位集合 `Φ_fresh`，作为“权重分离任意二维障碍”和“任意单黑格”定理的共同前提。

请 Codex 回复：

- 当前正在推进什么、正在编辑或计划编辑哪些文件；
- 对上述 2、3、4 的数学判断，尤其是否发现错误；
- 分工意见。Claude 的提议：Claude 在新文件 `BoundedMemory.lean` 中形式化 L1/L3 及分解定理，或者新建 `FreshPhases.lean` 计算 `Φ_fresh`；两者都只新增文件、不改动现有模块，并在本表登记后才开始。

## 2026-11-20 Codex → Claude（经 MCP 只读回合回复，由 Claude 摘录）

- (a) 同意两个等价归约，已独立复核编译。措辞意见：“等价”不等于“不可能更容易”；正向证明没用到 `EventuallyStandard s`，不代表可以删去这个前提。
- (b) 同意 L1、L3 与分解定理。修正意见：
  - L1 的强定义本身不需要有限支撑；
  - L3 需写明 `q > 0`、`C ≥ 0`、`T'' ≥ T`，并处理空集取最小值；
  - 分解的两个合取项不应称为“相互独立”；
  - 正向可直接从 `HighwayFrom` 推出弹道性，例如取 `p = 4`、`q = 104`、`C = 108`；
  - §3.1.5 还需控制块内部的波动。
- (c) 同意，但只限于“现有归纳不能直接闭合”这一说法。12080 只是已认证的入口，不是最早入口。§3.3.4 中“不对 n 一致”的理由有误。
- 分工：Codex 负责 `BoundedMemory.lean`、`FreshObstacleReduction.lean`、`Ballistic.lean` 及集成；Claude 负责 `FreshPhases.lean`。

## 2026-11-20 Claude → Codex

- 以上修正已全部并入 `research/claude-review.md`。
- 接受分工。`FreshPhases.lean` 第一阶段的交付目标：

  ```text
  ∃ K0 Φ, ∀ k ≥ K0, ∀ φ < 104,
    FirstVisitAt(seed, 104k+φ) ↔ φ ∈ Φ
  ```

  其中首次访问相对于从时刻 0 开始的整个历史；同时证明足够晚的目标格在种子初态中为白。有限扫描只用于发现候选，“对所有 `k ≥ K0`”由漂移与有限相位关系证明。先分类 `highwaySeed`，移植到全白初态时另行处理入口之前的历史。
- 不会修改 `lakefile.toml`；需要接入构建时在本文件告知 Codex。

## 2026-11-20 Claude → Codex：`FreshPhases.lean` 第一阶段完成

新增两个文件，未修改任何现有文件，也未修改 `lakefile.toml` 和 `.lake/`：

- `FreshPhases.lean`（只 `import FreshCollision`）
- `scripts/FreshPhaseChecks.lean`

主定理：

```lean
def FirstVisitAt (s : State) (n : Nat) : Prop :=
  forall j, j < n -> (run s j).pos ≠ (run s n).pos

theorem seed_firstVisit_iff {k phi : Nat} (hk : 2 <= k) (hphi : phi < 104) :
    FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ freshPhases

theorem seed_late_cell_white {k phi : Nat} (hk : 2 <= k) (hphi : phi < 104) :
    highwaySeed.toState.board (run highwaySeed.toState (104 * k + phi)).pos = false

theorem seed_fresh_phase_classification :
    exists K0 Phi, forall k, K0 <= k -> forall phi, phi < 104 ->
      (FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ Phi) ∧ ...（初始为白）
-- 取 K0 = 2
```

`freshPhases` 共 22 个相位：

```text
[4, 5, 6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 66, 94, 95, 96]
```

已认证的 4、5、66、94、95 都在其中；还缺恢复证书的有 17 个：

```text
6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 96
```

证明结构：

- 用 `checkPosTrace` 和 `decide +kernel` 把 104 个周期内位置的字面表对真实运行一次性认证；
- 由 `block_prefix` 得到 `pos(104q+j) = c_j + q·(-2,-2)`；
- 周期内权重范围是 `[-9,0]`（内核检查），所以 `k - q ≥ 3` 的更早周期不可能重合，只需检查同周期更早的相位以及前两个周期；
- 对所有 `k ≥ 2` 的结论由此对称证明，不依赖有限扫描；
- 白色部分来自种子黑格权重 `≥ -5`，而 `k ≥ 2` 时目标格权重 `≤ -8`。

检查结果：

- `FreshPhases.lean` 以 `-DwarningAsError=true` 编译通过。
- `scripts/FreshPhaseChecks.lean` 通过。它包括：与 `phaseFour_first_visit` 交叉验证；`k ≥ 2` 时相位 0 不是首访；符号变量 `k` 下相位 96 是首访；缺证书相位的列表。
- 公理只有 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorry` 或 `native_decide`。
- 检查脚本运行时，把 olean 输出到 Claude 的临时目录，并通过 `LEAN_PATH` 引用，没有写入 `.lake/`。

请 Codex 在集成时：把 `FreshPhases` 加入 `lakefile.toml` 的默认构建，在 `ProofAudit.lean` 中加入上面三个定理，并在 `proof-status.md` 中登记。

下一步（Claude）：为 17 个缺证书相位寻找 `RecoveryCertificate`，并检查 (C1) 恢复方向与 (C2) 读取下界。计划新增 `FreshPhaseRecovery.lean`；探索脚本放在 `scripts/` 下，不进入证明依赖。开始前会在上表登记。

## 2026-11-20 Claude → Codex：首访相位恢复（22 个中已认证 21 个）

新增四个根目录模块（均未接入 `lakefile.toml`），依赖链如下：

```text
FreshPhases → RotatedRecovery(import RecoveryCertificate, FreshPhases)
            → FreshPhaseRecovery(import MaturePhaseRecovery, FreshPhases, RotatedRecovery)
            → HardPhaseRecovery
```

主定理：

```lean
theorem fresh_phase_recovers_except_49 (phi : Nat) (hphi : phi ∈ freshPhases) (h49 : phi ≠ 49) :
    exists H, forall s, AgreesBelow 0 s highwaySeed.toState -> forall k,
      EventuallyStandard (flipCell (run s (104*(k+H)+phi)) (run s (104*(k+H)+phi)).pos)
```

新增的两种证书：

- `RotatedRecoveryCertificate`：新公路转向朝西北或朝东南，漂移权重为 0；无限尾部的权重界由一周期位置表推出。
- `checkShiftedRecovery`：先平移进位图窗口再检查，用于相位 38。

内核检查耗时（本机）：

| 文件 | 耗时 |
| --- | ---: |
| `FreshPhaseRecovery` | 约 600 s |
| `HardPhaseRecovery` | 约 295 s |

接入默认构建会明显增加 `lake build` 的时间，请 Codex 决定是否放进默认目标。

公理只有标准三个；四个文件中均无 `sorry`、`admit`、`native_decide`、`axiom`、`unsafe`。`scripts/FreshPhaseChecks.lean` 已改为 `import HardPhaseRecovery`，并打印各主定理的公理。

**相位 49 的现象（有限观察，未证明）：** 对所有测试过的 `H ∈ [11,25]`：

- 恢复入口固定在 `(39,-37)`，朝南；
- 延迟等于 `52213 + 104·(H-11)`；
- 最大权重为 7。

蚂蚁沿整条遗迹回到种子原始区域，因此不存在与历史无关的证书。下一步可考虑“沿周期遗迹逆行”的反向公路证书。这条线 Claude 可以接着做，计划新建 `TrailRetrace.lean`，开始前会在上表登记。

## 2026-11-20 Codex：续接任务 A

- 已核对任务文件、审阅和当前源码；中断前尚无任务 A 的集成改动。`BoundedMemory.lean` 现有部分已用 `tools/lean-4.36.0-windows/bin/lake.exe env lean -DwarningAsError=true BoundedMemory.lean` 检查通过，命令耗时 3.18 s。
- 本次编辑范围：`BoundedMemory.lean`、新建 `Ballistic.lean`、`lakefile.toml`、`scripts/ProofAudit.lean`、`drafts/proof-status.md`；验证辅助文件放在 `scratch-codex/`。不修改 Claude 占用的证明模块。
- 构建选择：轻量模块加入默认目标；`FreshPhaseRecovery`、`HardPhaseRecovery` 设为独立库目标 `FreshRecovery`。完整 `ProofAudit` 仍导入后者，执行前必须构建该目标。
- L1 沿用强定义，不添加有限支撑假设；L3 明示正分母、非负回退量与不早于原弹道起点的新起点，有限集合界使用锚点覆盖空集情形。

## 2026-11-20 Codex：任务 A 里程碑 L1

`BoundedMemory.lean` 已完成有限窗口枚举、有限值域重复引理、重复窗口的固定漂移，以及利用 `escapes_finite_set_after` 排除零漂移。主定理精确陈述：

```lean
theorem BoundedMemoryFrom.highway {s : State} {T W : Nat} (h : BoundedMemoryFrom s T W) :
    exists U P v, T <= U ∧ 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s U P v ∧
      forall n, U <= n -> readColor s (n + P) = readColor s n
```

另有 `EventuallyBoundedMemory.highway`，将存在起点和窗口宽度的前提转为相同的最终非零漂移结论。两者均不要求有限支撑，且不声称周期为 104。窗口有限性由 `memoryKey_mem` 给出显式列表，重复由 `finite_list_repeats` 证明，不依赖模拟。

验证命令：`tools/lean-4.36.0-windows/bin/lake.exe env lean -DwarningAsError=true -o .lake/build/lib/lean/BoundedMemory.olean BoundedMemory.lean`。退出码 0，实测 3.19 s。长计算目标 `FreshRecovery` 仍在构建，下一步完成 L3。

## 2026-11-20 Codex：任务 A 里程碑 L3 与分解定理

新增 `Ballistic.lean`。`BallisticFrom s T a b p q C` 使用整数系数，显式包含 `0 < p`、`0 < q`、`0 <= C`，并对所有 `T <= n <= m` 要求
`q * linearForm a b (run s m).pos <= q * linearForm a b (run s n).pos - p * ((m : Int) - (n : Int)) + q * C`。
正整数 `p,q` 表示正有理速率；整数非负 `C` 表示回退界。

```lean
theorem BallisticFrom.boundedMemory {s : State} {T : Nat} {a b p q C : Int}
    (h : BallisticFrom s T a b p q C) (hs : FiniteSupport s.board) :
    exists U, T <= U ∧ BoundedMemoryFrom s U ((q * C / p).toNat + 1)

theorem HighwayFrom.ballisticFrom_of_diagonal {s : State} {T : Nat} {v : Point}
    (h : HighwayFrom s T 104 v) (hv : DiagonalDrift v) :
    exists a b, BallisticFrom s T a b 4 104 108

theorem highwayConjecture_iff_ballistic_and_periodicIsStandard :
    HighwayConjecture ↔
      (forall s : State, FiniteSupport s.board -> Ballistic s) ∧ PeriodicIsStandard
```

`BallisticFrom.avoids_finite` 对任意有限列表成立；取最小值时加入整数锚点 0，空列表无需额外假设。L3 同时避开初始黑格支撑和时刻 `T` 之前的访问集合，故新起点 `U >= T`，且新格确实初始为白。正向弹道界直接从 `HighwayFrom` 的运动周期推出，未调用种子进入证书。两个分解合取项仍是开放命题，没有被当作已证事实或公理。

验证命令：`tools/lean-4.36.0-windows/bin/lake.exe env lean -DwarningAsError=true -o .lake/build/lib/lean/Ballistic.olean Ballistic.lean`。退出码 0，实测 2.69 s。接下来执行默认构建、长计算目标的完成检查、完整 `ProofAudit` 及新增边界检查。

## 2026-11-20 Codex B：开始相位 49 遗迹回溯

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `TrailRetrace.lean`、`scripts/ExploreTrailRetrace.lean` | Codex B | 已登记；先探索逆行阶段、端点和完整棋盘差异，再形式化 |

- 已读任务、证明状态和独立审阅；这两个任务 B 文件在本轮开始时均不存在，尚无需要续接的实现。
- 与任务 A 并行：不运行 `lake build`，不修改 `lakefile.toml` 或其他主线文件。编译采用 `tools\lean-4.36.0-windows\bin\lean.exe -o scratch-codex\...`，`LEAN_PATH` 包含 `scratch-codex` 和 `.lake\build\lib\lean`。
- 本里程碑只完成范围核对和占用登记；无新增定理，无构建执行或构建耗时。

## 2026-11-20 Codex B：探索里程碑，纠正回溯解释

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `TrailRetrace.lean`、`scripts/ExploreTrailRetrace.lean` | Codex B | 探索完成关键结构；正在构造避开历史差异的证书 |

- **以下仍是有限探索，不是定理。** `H=11,12,25,50,100` 均复现入口 `(39,-37)`、朝南和延迟 `52213+104*(H-11)`。但这不能证明沿旧遗迹回溯。
- 比较 `H=11` 与 `H=100`：前 52300 步位置在平移 `(-178,-178)` 后逐步相等，朝向和读色也全部相等；完整棋盘之差始终为同一组 1068 格，全部位于 `-2 <= x-y <= 8` 的旧公路窄带。第 51046 步开始已经出现周期 104、漂移 `(2,2)` 的运动（在所扫描的余下区间成立）。该段的 `x-y` 约为 75，远离旧公路窄带。因此当前证据支持在平行位置生成东北公路，而非沿旧公路返回原区。
- 在延迟 `52000+104*(H-11)` 的同姿态截面比较，完整棋盘差异依然很大：与 `H=11` 相比，`H=12` 有 2438 个差异格，`H=100` 有 6140 个。不能声称到达后的完整状态与历史长度无关。
- `H=11` 的 52213 步前缀坐标范围为 `x in [-63,41]`、`y in [-70,4]`，需要平移后才可使用现有 `[-64,64)^2` 位图窗口。前缀在 `weight>0` 且旧公路窄带内仅访问一次 `(2,-1)`，需精确检查这格的历史颜色，不能只用粗略半平面界。
- 执行命令：设置 `LEAN_PATH=D:\langtonsant\scratch-codex;D:\langtonsant\.lake\build\lib\lean`，运行 `tools\lean-4.36.0-windows\bin\lean.exe -DwarningAsError=true --run scripts/ExploreTrailRetrace.lean`。最近一次完整探索退出码 0，耗时 15.38 s。没有新增无限量化定理；下一步认证历史差异的支撑与有限前缀避让。

## 2026-11-21 Claude：接管全部工作

Codex 的额度已用尽，两个 Codex 线程停在以下状态，后续全部由 Claude 接管；上方占用表中 Codex 的条目一律视为 Claude 所有。

- **任务 A：** 默认构建已通过（94 项）。`FreshRecovery` 目标中的 `FreshPhaseRecovery` 已构建，`HardPhaseRecovery` 尚未构建；`ProofAudit` 尚未完整运行。`drafts/proof-status.md` 第 361 行仍沿用相位 49“沿遗迹返回原始区域”的旧解释，需要修正。
- **任务 B：** `TrailRetrace.lean` 只有框架，包括条带协议 `TrailAgreement`、种子轨迹始终在条带内、条带外始终为白，以及打包输入。核心的 52421 步证书尚未写出。上一次编译以 `0xC0000409` 退出，当时系统中多个进程同时崩溃，原因尚不确定。

## 2026-11-21 Claude：相位 49 完成，22 个首访相位全部认证

- `TrailRetrace.lean` 在 Codex B 草稿的基础上重写完成，并已加入 `FreshRecovery` 目标。`lake build FreshRecovery` 通过（54 项），其中 `TrailRetrace` 本身耗时 154 s。
- 主定理：
  - `phase_forty_nine_recovers`：前提为 `TrailAgreement 0 s highwaySeed.toState`，结论对每个 `k` 成立，从第 52421 步起进入漂移为 `(2,2)` 的标准公路。
  - `all_fresh_phases_recover`：覆盖全部 22 个首访相位。
  - 相位 49 的前提严格强于 `AgreesBelow 0`，因为新公路会进入 `x+y > 0` 区域。
- 证明结构：
  - 52421 步前缀（`decide +kernel`）在每一步都位于 `x+y ≤ 0` 或条带 `-2 ≤ x-y ≤ 8` 之外，末态在旋转后的完整半平面上与模板一致；
  - 尾部的 `x-y ∈ [68,78]` 对全部时刻由种子条带引理证明；
  - 更长的种子历史只在条带内不同。
- `scripts/ProofAudit.lean` 已改为 `import TrailRetrace`，审计 228 个定理，公理均为标准三个的子集，没有 `sorryAx`。默认 `lake build` 仍为 94 项，已通过。
- `drafts/proof-status.md` 中相位 49 的旧解释已替换为新的一节。

## 2026-11-21 Claude: single-black-cell theorem, progress at interruption (handoff)

**Done (compiled or kernel-checked):**
- `SingleBlackLate.lean` `singleBlack_late_explicit`: first contact time ≥ 13952 and phase ≠ 49.
- `WidePacked.lean` (256 window + mask agreement), `SingleBlackCheck.lean` (old-version certificate), `FastCell.lean` / `FastCell2.lean` (Nat-index certificates), `SingleBlackCover.lean` (coverage checker), `TreeBoard.lean` (binary-tree board; correct but slow, unused).
- `Phase49Blank.lean`: the whole proof compiles once its three heavy checks are stubbed with `sorry`. Not yet run for real: `checkBlankJunk_true`, `trail_prefix_junk_check`, `y49_run_check`. The repository copy contains `decide +kernel`, not `sorry`.
- `SingleBlackTheorem.lean`: written; only the symmetry part has been tested on its own.
- Near-cell certificates `SingleBlackEarly/`: 2168/2215 oleans are already in local `.lake/build/lib/lean/SingleBlackEarly/` (the remote ones are copied back).

**Unfinished:**
1. 34 large cells (FastCell2), run locally one at a time: `scratch-codex/f2-local-big.txt`.
2. 14 slow cells switched to the old-version certificate (FastCell / FastCell2 are pathologically slow on a few cells: C0898 took 2194 s with FastCell2 against 25 s with the old version), run on the remote one at a time: `scratch-codex/slow-old.txt`. Copy back to local when done.
3. Any large cell that times out also has to be switched to the old version (see how the slow list was generated).
4. Compile `SingleBlackEarly/G00..G59.lean` and `Cells.lean` (the `lean -o` LEAN_PATH approach), then the three heavy checks in `Phase49Blank`, then `SingleBlackTheorem`.
5. Audit axioms, scan for forbidden keywords, add the new modules to `lakefile`, update `proof-status.md` and the review.

**Notes:**
- Memory: one kernel check takes 1–6 GB. Always use `scripts/build_cells.py` (memory budget, watchdog, timeout); never `lake build` the whole `SingleBlackEarly` at once.
- Linux oleans have been verified to load on Windows.

## 2026-11-21 Claude：任意单黑格定理完成

- 主定理 `singleBlackAt_standard`（`SingleBlackTheorem.lean`）已证明，公理只有 `propext`、`Classical.choice`、`Quot.sound`。扩展后的 `ProofAudit` 共审计 234 个定理，全部干净。
- 新增模块：
  - 窗口与证书：`WidePacked`、`SingleBlackCheck`、`FastCell`、`FastCell2`、`SegmentCheck`、`TreeBoard`（未使用）；
  - 单黑格：`SingleBlackCover`、`SingleBlackCoverCells`、`SingleBlackLate`；
  - 相位 49：`Phase49Data`、`Phase49P1`/`K1`/`P2`/`Seg`/`K2_1..13`/`K2`/`P3`/`K3`、`Phase49Blank`；
  - `SingleBlackEarly/` 下 2215 个格子模块、178 个分段模块、60 个分组文件和 `Cells`。
- lakefile 中新增 `SingleBlackEarly` 与 `SingleBlackFull` 两个目标。不要直接 `lake build`，应使用 `scripts/build_cells.py`（控制内存）。
- 脚本：`find_single_black.py`、`gen_single_black*.py`、`gen_segments.py`、`gen_k2_segments.py`、`build_cells.py`。它们只负责生成参数和调度编译，不在信任链中。
- 已知问题：`FastCell`/`FastCell2` 在少数证书上内核极慢，原因尚未定位。

## 2026-11-21 Claude：FastCell 病态慢的原因已定位

单步函数里的 `let d := turn ...`，与每步对上一步投影所做的窗口检查叠加，会使内核耗时随步数大致按指数增长。去掉 `let` 后，`FastCell3.lean` 中的 `checkSingleBlackFast3` 用了 7.7 秒（Fast2 为 2194 秒），76377 步的大格子用了 27.9 秒且无需分段。新的定义与原定义相等，可靠性直接继承。今后的大规模证书应统一使用 Fast3。

## 2026-11-21 Codex C：续接与范围登记

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `PeriodicWord*.lean`、`scripts/PeriodicWordChecks.lean`、`lakefile.toml` 的任务 C 模块登记 | Codex C | 开始定义白背景自洽字及周期尾部归约 |

- 中断前仅检查了 Git 状态，尚无任务 C 实现；本次从当前 `single-black-cell` 分支的干净工作区开始。
- 已读任务、证明状态、审阅与协作记录。复用 `HighwayFrom.drift_ne_zero`、读色周期性及旋转平移对称性；不修改其他已有 Lean 模块。
- 首先证明有界重访计数确实覆盖双向无限路径，再证明有限支撑周期尾部的归约。奇数周期排除将尝试给出一般证明；外部枚举结果不进入证明依赖。
- 重型内核检查串行执行，不构建 `SingleBlackEarly` 或 `SingleBlackFull`。本条仅登记范围，无新增定理或构建结果。

## 2026-11-21 Codex C：里程碑 1，自洽字与奇数周期排除

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `PeriodicWordCore.lean`、`PeriodicWord.lean`、`scripts/PeriodicWordChecks.lean` | Codex C | 核心定义及辅助定理通过；正在完成历史访问与相位列表的双射 |

- `wordTrace w n` 从原点朝北按读色字行进，`wordDrift P w` 为周期末位置。`EarlierPhase a v i j` 表示 `j < i` 且同格，或存在正自然数 `t` 满足 `a j = a i + t*v`。非零漂移使每个相位至多贡献一次更早访问。
- `checkEarlierPhase_iff hv i j` 证明整数除法检查器与上述无界存在命题等价，负漂移和零横坐标均被覆盖。`period_overlap_bound hi hj hv he` 证明 `i,j<P` 时所有相交周期距离满足 `t <= 2*P`；没有截断遗漏的远期访问。
- 精确接口：`checkConsistentWord P w = true ↔ ConsistentWord P w`。后者要求末朝向为北、漂移非零，以及每个 `i<P` 的读色等于 `priorPhases P w i` 长度的奇偶。
- `ConsistentWord.even : ConsistentWord P w -> P % 2 = 0`；`no_consistent_word_odd : P % 2 = 1 -> forall w, ¬ ConsistentWord P w`。这是一般证明，不使用探索枚举。
- 已证明 `board_visit_parity` 和 `HighwayFrom.exists_white_copy`：有限支撑的正周期公路在每个固定相位都有任意晚的、初始为白的周期副本。主归约尚未完成。
- 编译使用 `LEAN_PATH=D:\langtonsant\.lake\build\lib\lean`，命令为 `tools\lean-4.36.0-windows\bin\lean.exe -DwarningAsError=true -o .lake/build/lib/lean/PeriodicWordCore.olean PeriodicWordCore.lean`，以及同式编译 `PeriodicWord.lean` 后运行 `lean.exe -DwarningAsError=true scripts/PeriodicWordChecks.lean`。最近一次后两项顺序运行退出码 0，合计 4.38 s。
- 审计上述检查器、计数界、奇数排除、棋盘奇偶和白色副本定理：仅 `propext`、`Classical.choice`、`Quot.sound` 的子集。小规模边界检查使用 `decide +kernel`，尚无重型穷举。

## 2026-11-21 Codex C：里程碑 2，主归约完成

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `PeriodicWordCore.lean`、`PeriodicWord.lean`、`scripts/PeriodicWordChecks.lean` | Codex C | 主归约已通过编译和公理审计；补充整数周期接口、有限检查与构建集成中 |

精确的主定理比任务要求略强：

```lean
theorem periodic_tail_consistent_at_start {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    ConsistentWord P (fun i => readColor s (T + i))

theorem periodic_tail_consistent {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    exists U, T <= U ∧ ConsistentWord P (fun i => readColor s (U + i))
```

- 第二条取 `U=T`。证明将 `run s T` 旋转平移到原点朝北；该操作保留读色，不需要改变字本身。
- 对每个相位，利用有限支撑和非零漂移选择任意晚的初始白色副本。`HighwayFrom.visits_phase_perm` 证明：当副本编号 `K >= 2*P` 时，所有真实更早访问按模 `P` 映射后，恰好是 `priorPhases` 的一个排列，且没有重复相位。这保证奇偶计数既无遗漏又无重复。
- 棋盘颜色由真实有限历史中的翻色奇偶给出；运动周期性将这个任意晚副本的读色传回原周期。没有将原起点之前的棋盘误设为全白，也没有用有限模拟证明无限尾部。
- 推论 `no_odd_periodic_tail hs hP hodd : ¬ HighwayFrom s T P v` 已证明。
- 验证命令：设置上述 `LEAN_PATH`，顺序运行 `lean.exe -DwarningAsError=true -o .lake/build/lib/lean/PeriodicWord.olean PeriodicWord.lean`、`lean.exe -DwarningAsError=true scripts/PeriodicWordChecks.lean`。退出码 0，合计 4.57 s。
- `#print axioms` 审计访问排列、两个主归约及奇数周期推论，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。无重型内核计算。

## 2026-11-21 Codex C：里程碑 3，组合分类接口与小周期内核结论

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `PeriodicWord*.lean`、`scripts/PeriodicWordChecks.lean`、`lakefile.toml` | Codex C | 全部定理及检查通过；默认构建集成验证中 |

- `biPeriodicPos P w k j = wordPos w j + k*wordDrift P w` 明确定义双向整数周期路径。`mem_priorPhases_iff_integer_period` 把列表成员与 `exists k : Int, k*P+j<i ∧ biPeriodicPos P w k j=wordPos w i` 等价起来；`biPeriodicPos_injective_period` 证明非零漂移下固定相位的周期编号唯一。因此列表长度确实计数全部更早访问，而非只记录是否访问过。
- 新增纯组合待证命题 `ConsistentWordsAreStandard`：对每个正 `P` 和自洽字 `w`，存在 `a<P`，使全部 `n<104*P` 满足 `w ((a+n)%P)=certifiedColor n`。窗口为两周期的公共倍数；`finite_word_standard_extends` 证明有限比较自动延伸到全部自然数。
- `consistentWordsAreStandard_implies_periodicIsStandard` 和 `highwayConjecture_of_ballistic_and_consistentWordsAreStandard` 已证明。只给出充分归约，不声称逆向等价，也不把该分类命题设为公理。`standard_word_consistent` 给出标准 104 位字的正例。
- `PeriodicWordEnumeration.lean` 以位编码覆盖任意 `Nat -> Bool` 字在 `i<P` 的前缀，并证明检查器穷举的可靠性。偶数 `2,4,6,8,10,12` 已用 `decide +kernel` 排除，结合全部奇数排除得到：

```lean
theorem no_consistent_word_small (P : Nat) (h1 : 0 < P) (h2 : P <= 13) (w : Nat -> Bool) :
    ¬ ConsistentWord P w

theorem no_periodic_tail_small {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 13) : ¬ HighwayFrom s T P v
```

- 内存实测：早期 `P<=8` 检查 3.33 s，采样峰值私有内存 1307 MiB；最终整数编码 `P=10` 检查 9.29 s，1840 MiB。整块 `P=12` 尝试被内存守卫终止，没有使用它的未完成结果。
- `P=12` 改为 8 个模块，每块 512 个编码，按 A 至 H 的导入链串行。各块实测耗时为 5.79、6.48、5.36、5.21、5.08、4.97、5.00、5.34 s；采样峰值私有内存 1489–1538 MiB，最低可用物理内存 3.16 GiB。每次命令均为 `lean.exe -M1536 -DwarningAsError=true -o .lake/build/lib/lean/<module>.olean <module>.lean`，辅以每 200 ms 检查可用物理内存/提交空间及进程私有内存的守卫，退出码全部为 0。
- 新库目标 `PeriodicWords` 已加入默认目标，设置 `moreLeanArgs = ["-M1536", "-DwarningAsError=true"]`；证书导入链确保 Lake 无法并发运行这些重型检查。其他既有库配置未改动。
- 最后顺序编译 `PeriodicWordReduction`、`PeriodicWordCheck12`、`PeriodicWordSmall` 并执行 `scripts/PeriodicWordChecks.lean`，共 8.11 s，退出码 0。脚本审计 20 个定理，公理均仅标准三个的子集；另检查零周期、奇数周期、漂移正负/零横坐标、标准字正例、任意旋转平移及任意起点的小周期排除。

## 2026-11-21 Codex C：里程碑 4，任务完成与最终验证

| 文件 | 占用方 | 状态 |
| --- | --- | --- |
| `PeriodicWord*.lean`、`scripts/PeriodicWordChecks.lean`、`lakefile.toml` 的任务 C 集成 | Codex C | 完成；已验证，可供后续工作使用 |

- `tools\lean-4.36.0-windows\bin\lake.exe build` 默认构建成功，共 129 项，实测 63.54 s；本轮新增的 16 个根模块全部经 Lake 重建。重型内核证书按导入链串行，运行中检查到一个 Lean 编译进程；构建期间采样最低可用物理内存 3.68 GiB。构建范围为默认 `LangtonsAnt`、`PeriodicWords`，未构建 `SingleBlackEarly` 或 `SingleBlackFull`。
- 构建后执行 `tools\lean-4.36.0-windows\bin\lake.exe env lean -M1536 -DwarningAsError=true scripts/PeriodicWordChecks.lean`，退出码 0，实测 2.31 s。20 个定理的公理依赖均仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。
- 新增 Lean 文件的 `sorry`、`admit`、`native_decide`、自定义 `axiom`、`unsafe`、`implemented_by`、`extern` 扫描无命中，`git diff --check` 通过。
- 最终证明范围：有限支撑正周期尾部在原起点即给出白背景自洽字；全部奇数长度排除；所有 `1 <= P <= 13` 的自洽字及有限支撑最终周期排除；标准 104 位字为正例；纯组合分类条件充分推出 `PeriodicIsStandard`。
- 尚未证明该组合分类条件本身，也未证明所有自洽字都来自有限支撑实际轨迹。因此这里不声称分类条件与 `PeriodicIsStandard` 等价，不声称一般有限支撑猜想成立。外部 `P=14..36` 的探索结果没有进入证明依赖。

## 2026-11-21 Codex：接手后续工作

- 用户已返回并授权接手；已读取 Claude 项目记忆、当前任务和本记录，当前分支工作区干净。单黑格定理与既有结果的 `ProofAudit.lean` 重新通过。
- 本轮范围：新增 `PeriodicWordRealization*.lean`，补充 `PeriodicWordReduction.lean`、`scripts/PeriodicWordChecks.lean`、`lakefile.toml` 与 `drafts/proof-status.md`。不修改单黑格的重型计算证书。
- 目标：证明每个正长度的白背景自洽字均可由有限支撑初态实现，再将组合分类条件与 `PeriodicIsStandard` 连接为等价关系。使用指定读色的辅助轨迹建立有限前缀棋盘，然后证明足够晚的读取都符合真实规则；辅助轨迹本身不被假定为实际运行。
- 本轮采用符号证明，不需要扩大内核枚举范围或使用 `native_decide`。

## 2026-11-21 Codex：有限实现与双向归约完成

- `PeriodicWordRealizationTrace.lean` 在尚未假定读色合法的指定转向路径上证明周期平移、同相位访问唯一性及完整先前访问列表的排列对应。周期编号 `K >= 2*P` 后，该列表恰好对应自洽定义中的 `priorPhases`。
- `PeriodicWordRealization.lean` 定义有限前缀翻色棋盘及初态 `wordRealization P w`。`ConsistentWord.realization_run` 证明从该初态开始，实际无限运行与指定路径一致；`ConsistentWord.realizable` 给出有限支撑、从时刻 0 起的周期漂移及逐步精确读色。`wordRealization_support_bound` 用长度 `2*P*P` 的列表覆盖全部初始黑格。前缀构造不被冒充为全白初态的实际运行。
- `consistentWord_iff_finite_realization` 补齐自洽条件与有限实现的双向关系。`PeriodicWordReduction.lean` 新增 `periodicIsStandard_iff_consistentWordsAreStandard` 及 `highwayConjecture_iff_ballistic_and_consistentWordsAreStandard`。这更新了里程碑 4 的边界：自洽字的有限可实现性已证明，组合分类现在是等价条件；分类本身和全体有限初态的弹道性仍未证明。
- `scripts/PeriodicWordChecks.lean` 增加 8 项公理审计，共 28 项，均仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。额外检查标准字有限实现的 21632 长度支撑覆盖，以及将输入字在第 104 位之后全部取反仍不改变实现读色。脚本以 `-M1536 -DwarningAsError=true` 运行，退出码 0，耗时约 2.46 s。
- 默认 `lake build` 成功，共 133 项，耗时约 7.38 s。本轮重新构建两个新增模块及归约模块，其余沿用已验证缓存；没有重跑单黑格重型证书。新模块已经加入 `PeriodicWords` 默认构建目标。
- `git diff --check` 通过；本轮涉及的 Lean 文件中 `sorry`、`admit`、自定义 `axiom`、`native_decide`、`unsafe`、`implemented_by`、`extern` 扫描无命中。`drafts/proof-status.md` 已记录构造、定理和边界。
