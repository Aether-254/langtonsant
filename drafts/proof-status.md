# Lean 形式化状态

更新日期：2026-11-22。各轮旧验证记录按原范围保留，最新一轮的范围见文末“双前沿探索”。

## 当前结论

已完成 Lean 证明：任意棋盘的轨迹无界、通用公路延续证书的可靠性、显式 23 黑格种子的无限标准公路、全白初态从第 12080 步起的无限标准公路，以及这两个具体轨迹的读色最小周期为 104。

后续已补齐四方向旋转与平移、标准读色轨迹的耦合定理、有限初态的“最终标准公路当且仅当最终进入半平面证书”、可执行检测器的可靠性和完备性，以及原始猜想与该检测器对任意有限输入最终成功的等价关系。另证明了分离初态族、单黑格无统一进入时间上界、有限扰动的首次接触判定、原猜想与脚下单格翻色稳定性的等价关系，以及三个具体碰撞恢复结论和其中一个允许任意外围颜色的无穷初态族。一般猜想仍未得到无条件证明。

最新增加：通用恢复证书及有限棋盘到位图的可靠编码；六个固定相位的历史恢复定理；第二条显式单黑格恢复坐标族；以及任意数量、在初始时刻全部放置、逐个发生碰撞并恢复的多黑格初态族。多障碍族已证明每个初始黑格的首次访问时间，以及最终永久公路的线性充分起点。

无限支撑扩展：把该障碍链延伸为单向无限链后，已构造每 548 步平移 `(-8,-8)` 的非标准公路。此状态不满足有限支撑，且不能在任意更晚时刻进入标准 104 步公路。另证明有限障碍链在任意固定观察时长内最终与无限链完全相同；有限支撑初态的最终标准行为不能通过这种极限推出无限链的最终标准行为。

可变间距扩展：对每个自然数 `k`，间距为 `8+2*k` 的单向无限障碍链已证明从第 12496 步起具有周期 `548+104*k`、位移 `(-8-2*k,-8-2*k)`。最新结果已确定：对所有 `k`，这都是精确的最小最终正周期，读色序列和包含朝向的平移运动均如此。所有最终读色周期恰好是 `548+104*k` 的非负整数倍；所有最终公路的周期与位移恰好是上述周期、位移对的相同倍数。不同参数的平均速度不同，所有成员均排除任何最终 104 步周期。

独立间距扩展：每一段的参数可以分别选择，不再要求全链等距。任意有限间距列表已证明最终恢复标准公路，并给出显式充分起点。对无限序列，只要在任意晚处仍有任意大的间距参数，就没有任何最终正读色周期，也没有任何最终平移公路。显式例子的黑格为 `(-68-i*(i+7),-42-i*(i+7))`，其每个有限截断都最终标准，而无限初态永不最终周期；有限观察窗口的精确一致也已证明。

精确恢复扩展：独立间距有限链与无限链的每个障碍均已证明首次在 `12604+T_i` 被访问。保留 `p_0,...,p_n` 时，永久 104 步位置平移与朝向重复的最早起点恰为 `12915+T_n`，位移 `(-2,-2)`；更早时刻对任何位移都不成立。标准参考字的相位对齐证书可提前到 `12940+T_n`。这里 `T_n` 为前 `n` 个碰撞及间隔模块的总时间。

“任意有限黑格初态最终进入标准 104 步公路”仍未证明。`HighwayConjecture : Prop` 和 `Period104Conjecture : Prop` 仍为未解决的命题定义，没有被设为公理。文献核查见 `research/highway-conjecture-status.md`。

任务 A 新增：主猜想与“增加初始黑格稳定性”“首访障碍稳定性”的两个等价归约已接入构建。**任意单黑格初态（任意位置、朝向）最终进入标准公路已完整证明**（`singleBlackAt_standard`）。标准种子共有 22 个成熟首访相位，全部已认证最终恢复：其中 21 个在保护半平面外历史任意时成立；相位 49 在历史仅于旧公路条带内、权重为正处与种子不同的条件下成立（`all_fresh_phases_recover`）。另已完成强有界记忆推出非零漂移周期公路的 L1、有限支撑加弹道性推出强有界记忆的 L3，以及主猜想的“普遍弹道性与周期分类”分解。上述结构性定理不证明两项开放条件成立，也不把未知周期指定为 104。

全部主要证明位于根目录：`LangtonsAnt.lean` 定义原始模型和无界性；`FiniteAnt.lean` 证明黑格列表实现的一致性；`Highway.lean` 证明通用公路延续；`HighwayChecker.lean` 证明有限检查器的可靠性；`StandardHighway.lean` 给出具体种子与最小周期；`PackedAnt.lean` 证明带越界拒绝的位图实现的一致性；`BlankHighway.lean` 将全白初态连接到已认证的标准公路。

新增根目录模块：`Symmetry.lean` 处理四个旋转方向和坐标归一化；`TrajectoryCoupling.lean` 证明相同读色导致相同运动，并保持初始逐点颜色一致；`HighwayEntrance.lean` 给出进入证书与最终标准公路的等价关系；`EntranceChecker.lean` 实现并证明有限步检测器；`SeparatedInitialStates.lean` 证明一类黑格可任意多且位置无界的初态；`DelayedHighway.lean` 证明单黑格也能排除任意预设的起始时间上界。

首次接触与恢复相关模块：`FirstContact.lean` 保留扰动前后的完整棋盘历史，证明首次接触前精确耦合、接触时相反读色和下一步相反朝向；`FirstContactDecision.lean` 给出与全白参考轨迹是否相交的总判定程序；`SingleFlipReduction.lean` 给出一般猜想的脚下翻色等价归约；`CollisionRecovery.lean` 证明具体恢复证书及其外围扰动推广。

历史相关恢复模块：`HighwayRecovery.lean` 证明任意证书入口之后 `208 + 104*k` 步的脚下翻色在 592 步后恢复；`FreshCollision.lean` 证明周期内相位 4 的翻色在 440 步后恢复，以及该相位的目标格此前未被访问；`DelayedRecovery.lean` 将这些结果连接到从全白背景出发的显式单黑格初态族。

本轮新增根目录模块：`PackedFinite.lean` 证明有限列表棋盘的位图编码；`RecoveryCertificate.lean` 把有限恢复证书推广到任意后续周期、旋转和入口位置；`MaturePhaseRecovery.lean` 认证相位 5、66、94、95 并证明第二条单黑格坐标族；`MaskedAgreement.lean` 在保留全部历史的同时显式携带未访问的初始扰动；`ObstacleChain.lean` 证明单个障碍的 548 步转移及任意次数组合；`MultipleObstacles.lean` 把组合定理应用于全白背景上的任意数量初始黑格。

无限链相关模块：`InfiniteObstacleHighway.lean` 定义无限棋盘、证明 548 步公路证书、无限支撑和排除标准公路；`InfiniteHighwayPeriod.lean` 验证最小周期；`InfiniteChainLimit.lean` 证明有限链与无限链在有限观察时间内的精确一致。

`SpacedObstacleHighway.lean` 把无限链推广到所有偶数间距 `8+2*k`，证明通用周期证书、从原点朝北的初始障碍链到证书入口的可达性、不同平均速度、排除标准公路，以及任意大最小最终周期的存在。

`SpacedHighwayWord.lean` 认证碰撞读色字与六位标记的有限检查；`SpacedHighwayPeriod.lean` 将标记的唯一位置推广到全部参数；`SpacedHighwayClassification.lean` 连接实际轨迹，证明精确最小周期及全部最终周期、位移的分类。

`VariableObstacleBlock.lean` 证明任意后续掩码下的一段转移；`VariableFiniteObstacles.lean` 证明各段独立选择间距的有限链恢复；`VariableInfiniteObstacles.lean` 证明任意无限间距序列的逐段入口；`AperiodicObstacleChain.lean` 证明间距无界时没有最终正周期；`VariableChainLimit.lean` 连接有限截断与无限轨迹。

`VariableFirstVisits.lean` 证明独立间距链的首次访问和有限链各段读色；`VariableRecoveryBounds.lean` 排除最后一次首次接触之前的任何正周期公路，并证明有限截断的进入时间无界；`ExactVariableRecovery.lean` 给出通用公路向前延伸引理以及该有限链族的精确 104 步公路起点。

任务 A 接入的模块为 `FreshObstacleReduction.lean`、`FreshPhases.lean`、`RotatedRecovery.lean`、`FreshPhaseRecovery.lean`、`HardPhaseRecovery.lean`、`BoundedMemory.lean` 与 `Ballistic.lean`。其中长计算恢复证明 `FreshPhaseRecovery`、`HardPhaseRecovery` 与 `TrailRetrace` 使用独立构建目标 `FreshRecovery`（`lake build FreshRecovery`，本机约 15 分钟），其余加入默认目标。完整 `scripts/ProofAudit.lean` 依赖该目标，本次审计 228 个定理，公理依赖均为 `propext`、`Classical.choice`、`Quot.sound` 的子集。

## 已形式化的模型与定理

- `Point = Int × Int`：无限方格，不引入有限边界或环面。
- `Board = Point -> Bool`：`false` 为白，`true` 为黑。`step` 先按当前颜色转向，再翻转当前格并前进；白格右转，黑格左转。
- `FiniteSupport`：黑格包含在某个有限列表中。允许任意初始位置和四种朝向；列表可以包含重复项，不影响集合有限性的含义。
- `finiteSupport_run`：任意有限步之后，有限支撑仍有限；没有声称黑格数随时间有统一上界。
- `axisParity_run`、`same_cell_same_axis`：位置棋盘奇偶性和朝向轴绑定，因此同一格的到达轴固定。
- `escapes_finite_set`：对任意初始棋盘和任意有限格子列表，存在一步落在列表外。
- `escapes_finite_set_after`：对任意时间下界 `T`，仍有 `n >= T` 落在给定有限集合外。

逃逸定理甚至不要求初始黑格有限。它只证明访问集合无界，不能推导每格仅被访问有限次、距离趋于无穷，或者任何周期性。

## 证明结构

假设轨迹被有限列表覆盖。`recurrent_tail` 排除每个仅有限次出现的点，得到某个时刻之后只访问无限次出现的点。`finite_range_recurrent_max` 在这些点中选取 `x+y` 最大的点。

该点的北、东邻居不可能在此后的轨迹中出现。固定到达轴和局部运动规则通过 `corner_color` 强制每次访问读取同一种颜色；`recurrent_not_fixed_color` 利用每次访问翻色证明这是不可能的。由此推出有限区域逃逸。

## 公路证书及其无限延续

令 `weight (x,y) = x+y`。`AgreesBelow c s t` 要求两个状态位置和朝向相同，并在整个半平面 `x+y <= c` 上颜色逐点相同。

`HighwayCertificate seed P v c` 要求：`P > 0`、`weight v <= 0`、一个周期内所有读取格都位于 `weight <= c`，且运行 `P` 步后在 `weight <= c + weight v` 的半平面上与平移后的初始模板一致。这里没有直接假设未来无限运动重复。

`HighwayCertificate.blocks` 对周期次数归纳，`block_prefix` 覆盖周期内部每一步，得到 `highway`、`reads` 和 `all_bounded`：所有未来位置与朝向周期平移、读色周期重复，且永远留在原始半平面内。

`highway_of_matches`、`reads_of_matches`、`highway_of_entry` 允许保护半平面外存在任意历史遗迹，包括无限配置。半平面内部必须满足完整匹配，不能只检查几个重复周期。

`highwaySeed` 有 23 个互异黑格，蚂蚁位于原点朝北。`highwaySeed_check` 用 `decide +kernel` 检查周期 104、漂移 `(-2,-2)`、界限 0 的证书。`highwaySeed_highway`、`highwaySeed_exact_reads` 证明无限运动和完整读色序列。`highwaySeed_minimal_read_period` 排除了全部 `1 <= q < 104` 的读色周期。23 仅是本证书的种子大小，不是最小黑格数结论。

`blank_entry_check` 通过内核计算确认：全白初态第 12080 步的位置为 `(-56,-30)`、方向朝北，且整个 `x+y <= -86` 半平面与平移后的种子一致。因此得到完整定理：

```lean
theorem blank_standard : StandardHighwayFrom blank 12080 (-2, -2)
```

12080 是本次选取的充分进入时刻，不是最早公路起点。`blank_minimal_read_period` 排除了从此刻起读色序列的更短正周期。

`standard_highway_of_entry` 对任意状态、时刻和模板原点证明：满足这个半平面匹配条件就永久执行西南向标准公路。`EntryAt.standard` 进一步覆盖四个旋转方向。尚未证明任意有限初态必然满足进入条件。

## 进入证书的完备性与检测器

`EntryAt s T r origin` 表示把时刻 `T` 的棋盘平移、旋转到标准坐标系后，在整个 `x+y <= 0` 半平面上与 23 黑格模板一致。坐标原点和旋转不是额外需要枚举的自由参数：`EntryAt.pose_fields` 证明它们由当前蚂蚁的位置和朝向唯一确定。

`run_coupling` 证明：两个状态起始位置、朝向相同且读取颜色序列完全相同，就执行相同运动，并且每个初始颜色一致的格子在所有后续时刻仍一致。对于两个有限初态，初始颜色差异仅可能位于一个有限集合内。标准公路的前端每周期向西南移动，使保护半平面最终避开这个有限差异集合。由此证明反向命题，得到：

```lean
theorem eventuallyStandard_iff_enters (hs : FiniteSupport s.board) :
    EventuallyStandard s ↔ EventuallyEnters s
```

这里的有限支撑前提不可从该证明中去掉；无限分布的差异未必全部落到前端后方。该等价关系是对当前证书完备性的证明，没有证明标准轨迹一定开始。

`checkEntry` 直接将有限棋盘按当前蚂蚁位置和朝向归一化，然后检查半平面匹配。`searchEntry fuel s` 搜索包含端点的时刻范围 `[0, fuel]`，返回 `some T` 或 `none`。每次有界搜索本身都终止；`none` 仅表示该有限范围内没有找到证书，不能作为反例。

`searchEntry_sound`、`searchEntry_complete` 与 `eventuallyStandard_iff_search` 证明：搜索成功必然意味着进入无限标准公路，而任何最终进入标准公路的有限初态必然在某个有限搜索范围内成功。

`finiteSupport_representable` 证明原始模型的每个有限支撑状态都有精确的有限列表表示，因此没有遗漏可用有限输入。最终得到：

```lean
def DetectorEventuallySucceeds : Prop :=
  forall s : FiniteState, exists fuel T, searchEntry fuel s = some T

theorem highwayConjecture_iff_detectorEventuallySucceeds :
  HighwayConjecture ↔ DetectorEventuallySucceeds
```

`DetectorEventuallySucceeds` 仍是未解决的命题定义。等价重述没有降低原始猜想的逻辑强度，也没有给出成功时间上界。另有 `highwayConjecture_iff_standardTraceConjecture`，证明只要完整标准读色尾部出现，漂移方向由当时朝向确定，无需额外假定位置周期。

## 无穷初态族与时间上界的限制

`blank_all_bounded` 证明全白初态的整个轨迹始终位于 `x+y <= 126`。前 12080 步使用已验证位图运行的边界信息；后续无限尾部使用半平面公路证书。126 是一个足够的上界，没有声称它最优。

`standard_of_separated_black_cells` 证明：蚂蚁从原点朝北出发，只要每个初始黑格都满足 `x+y > 126`，就从第 12080 步起运行标准公路。黑格数和坐标不设上界；更强的 `standard_of_white_below` 甚至允许外侧存在无限黑格。`standard_of_white_in_frame` 把结论推广到任意初始位置和朝向的归一化坐标系。

这类黑格永远不会被全白轨迹访问，所以它们不会改变该轨迹。这一族没有覆盖黑格干扰蚂蚁运动的核心情形。

`DelayedHighway.lean` 给出另一种可严格证明的限制：

```lean
theorem one_black_unbounded_delay (N : Nat) :
  exists p : Point, forall T, T <= N -> forall v,
    ¬HighwayFrom (singleBlack p) T 104 v
```

`singleBlack p` 是原点朝北、恰好在 `p` 处放置一个黑格的初态。证明从全白轨迹的无界性选取一个很晚才首次被访问的格子，把黑格放在该处。首次接触前，两条轨迹相同；接触时，一条读黑、一条读白。全白轨迹此时早已满足 104 步周期，因此修改后的轨迹在相隔 104 步的两次读色上发生冲突，排除任意 `T <= N` 的永久 104 步公路。

该定理不证明所选单黑格初态最终仍会进入公路，也不提供碰撞后的恢复时间。它证明仅依赖初始黑格数量的统一起始时间上界不存在；若要给出统一上界，至少还须控制空间位置或范围，或者采用不需要统一时间上界的论证。

## 首次接触的精确归约和总判定

`perturb mask s` 保持位置和方向，把棋盘逐点异或一个固定掩码。`FirstContact mask s T` 表示参考轨迹在时刻 `T` 首次读取掩码为真的格子。对任意棋盘和掩码，`firstContact_state` 证明：

```lean
run (perturb mask s) T = perturb mask (run s T)
```

等式右侧包含参考运行在此前生成的全部历史遗迹，并未把参考棋盘重置为白色。首次接触之前读色和运动一致；首次接触时读色相反，下一步朝向相反。若永远没有接触，则完整位置、方向和读色轨迹永久一致，已知标准公路可以直接转移到扰动状态。

对于有限格子列表 `cells`，令 `m = min({0} ∪ {x+y | (x,y) ∈ cells})`。`blank_tail_weight` 证明全白轨迹在 `12080 + 104*k + j` 时刻（`j < 104`）满足 `x+y <= -86 - 4*k`。因此在保守界限

```text
B(cells) = 12080 + 104 * (max(0, -m) + 1)
```

之后，全白轨迹不再访问列表中的任何格子。`decideBlankContact cells` 只需搜索 `[0, B(cells))`，即可对无限参考轨迹给出完整结论：

- `some T` 当且仅当 `T` 是首次接触时间；由 `decideBlankContact_some_iff` 证明。
- `none` 当且仅当参考轨迹永远避开该列表；由 `decideBlankContact_none_iff` 证明。
- 返回 `none` 时，以这些格子为初始黑格的原点朝北状态，已证明从第 12080 步开始标准公路。

这个程序是“是否及何时首次接触全白参考轨迹”的总判定程序，不是碰撞后是否恢复公路的总判定程序。界限依赖格子坐标，与单黑格也可以任意晚才接触的结论相容。

## 脚下翻色的等价归约

`flipCell s p` 只翻转当前棋盘在 `p` 的颜色，保持位置和方向。未解决的命题 `CurrentCellFlipStability` 明确量化全部有限支撑状态：

```lean
def CurrentCellFlipStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    EventuallyStandard (flipCell s s.pos)

theorem highwayConjecture_iff_currentCellFlipStability :
  HighwayConjecture ↔ CurrentCellFlipStability
```

反向证明分两步。首先，翻转任意远处格子时，若参考轨迹永远不读取它，运动不变；否则运行到首次读取时，再应用脚下翻色稳定性。这一步保留参考运行生成的完整历史状态。其次，对有限黑格列表归纳，从任意位置、方向的全白状态开始，逐格翻色；重复列表项按集合语义处理。由此恢复原始一般猜想。

`CurrentCellFlipStability` 只是命题定义，没有证明，也没有设为公理。该等价关系不能被“23 黑格种子翻转后会恢复”替代：量词包括所有最终进入标准公路的有限状态、所有过渡阶段和已经生成的全部历史棋盘。有限支撑也不意味着运行后只剩原来的有限个障碍。

`FreshObstacleReduction.lean` 进一步完成两个精确的收窄等价：

```lean
def AddBlackStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall q, s.board q = false -> EventuallyStandard (flipCell s q)

def FreshObstacleStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall T, s.board (run s T).pos = false ->
      (forall j, j < T -> (run s j).pos ≠ (run s T).pos) ->
      EventuallyStandard (flipCell (run s T) (run s T).pos)

theorem highwayConjecture_iff_addBlackStability :
    HighwayConjecture ↔ AddBlackStability
theorem highwayConjecture_iff_freshObstacleStability :
    HighwayConjecture ↔ FreshObstacleStability
```

反向归纳只需向初始白格增加黑色障碍；首次接触耦合把它转成保留全部历史的脚下翻色。首访时刻可以位于公路出现之前的过渡阶段，因此仅证明已进入公路后的相位恢复不能完成该归纳。两种稳定性仍为开放命题，等价归约本身不声称已经降低逻辑强度或证明一般恢复。

## 已认证的碰撞恢复

`CollisionRecovery.lean` 已给出以下永久标准公路结论，时间均为经过证明的充分起点，不主张最早：

| 初态（原点朝北，除所列黑格外均白） | 标准尾部起点 | 每 104 步漂移 | 验证方式 |
| --- | ---: | --- | --- |
| 唯一黑格 `(0,0)` | 12081 | `(2,-2)` | 一步后棋盘全白、位置 `(-1,0)` 朝西，复用旋转后的全白定理 |
| 唯一黑格 `(1,0)` | 2905 | `(-2,2)` | 带越界拒绝的位图运算和完整半平面入口证书，均经内核验证 |
| 23 黑格种子的脚下黑格翻白，得到 22 黑格初态 | 276 | `(-2,-2)` | 列表实现运行后验证整个 `x+y <= -4` 半平面与平移种子一致 |

第二例在时刻 1 首次读到初始黑格，确实改变参考路线。验证时把初态旋转至最终公路朝西南，证书原点为 `(-16,-7)`；随后用已证明的旋转等变性还原到原坐标系，原坐标入口为 `(-7,16)`、朝东。

第三例还有无穷族推广。`flippedHighwaySeed_bound_check` 经内核验证前 276 步始终位于 `x+y <= 7`，无限公路尾部位于 `x+y <= -4`，从而得到：

```lean
theorem standard_seed_flip_recovers_of_matches
    (h : AgreesBelow 7 s highwaySeed.toState) :
  StandardHighwayFrom (flipCell s s.pos) 276 (-2, -2)
```

这允许 `x+y > 7` 的区域有任意颜色，包括任意多的有限黑格，甚至无限黑格。恢复前会改变路线，恢复后永久运行公路，因此超出了“所有初始黑格都不被访问”的情形。要求匹配整个 `x+y <= 7` 半平面；仅有原公路的 `x+y <= 0` 匹配不能套用这个立即翻色结论。下面的新定理通过先让公路运行足够时间，得到两个不再要求该额外条带匹配的恢复结论。

## 任意长公路历史的固定相位恢复

`HighwayRecovery.lean` 对 `highwaySeed` 已运行 208 步的完整状态进行脚下翻色，内核验证恢复前 592 步均处于 `x+y <= -2`，恢复入口为 `(-10,-10)`、朝北，之后无限尾部位于 `x+y <= -20`。历史棋盘没有被删除或截断。

利用 `HighwayCertificate.blocks` 和保护半平面的运行耦合，可以把该有限恢复证书推广到所有周期编号：

```lean
theorem highway_flip_recovers_after_two_periods
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
  StandardHighwayFrom
    (flipCell (run s (104 * k + 208)) (run s (104 * k + 208)).pos)
    592 (-2, -2)
```

这里只要求原始公路入口的 `x+y <= 0` 匹配，原始保护半平面外允许任意历史颜色。`k` 是未限制的自然数；不是穷举有限多个周期。`EntryAt.flip_recovers_after_two_periods` 进一步覆盖任意入口时刻、旋转方向和平移位置。

`EventuallyStandard.late_flip_recovery` 因而证明：对任意有限支撑、已知最终进入公路的状态，存在一个时刻 `T` 和方向 `r`，在所有时刻 `T + 104*k` 分别翻转脚下格后，都能从该扰动状态的第 592 步起永久恢复同向公路。这里每个 `k` 对应从原参考轨迹施加一次独立扰动，没有声称在同一次运行中每隔 104 步连续扰动也能恢复。

`FreshCollision.lean` 对周期内相位 4 给出另一张恢复证书：从 `run highwaySeed 4` 翻色，440 步内轨迹始终处于 `x+y <= 0`，随后在 `(-6,-6)` 接回标准公路。推广得到：

```lean
theorem highway_flip_recovers_at_phase_four
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
  StandardHighwayFrom
    (flipCell (run s (104 * k + 4)) (run s (104 * k + 4)).pos)
    440 (-2, -2)
```

其旋转、平移和入口时间版本为 `EntryAt.flip_recovers_at_phase_four`。这些是最先证明的两个相位；下面的通用恢复证书再增加相位 5、66、94、95。六个相位的结果仍不蕴含任意当前状态的 `CurrentCellFlipStability`。

## 显式的延迟碰撞与恢复单黑格族

对任意 `k : Nat` 定义

```text
p(k) = (-66 - 2*k, -40 - 2*k)
t(k) = 12500 + 104*k
```

初态是全白背景、唯一黑格在 `p(k)`、蚂蚁从原点朝北。`delayedObstacle_first_visit` 证明全白参考轨迹在 `t(k)` 首次访问这个格子。完整证明分为两段：前 12080 步的已验证位图运行始终在 `[-64,64)^2` 内，因此不可能访问横坐标小于 -64 的 `p(k)`；之后用公路周期归纳及 `phaseFour_first_visit` 排除全部更早访问。

`phaseFour_first_visit` 通过一个周期内的有限几何检查推广到全部周期：相位 4 的位置为 `(-2,-2)`；当前周期更早的四个位置均不同；标准周期中的对角格满足横坐标严格大于 -4，因此任何更早周期的平移副本也不能提前访问该目标。该论证没有把读白等同于首次访问。

`delayedObstacle_contact_state` 在碰撞时将单黑格初态的完整运行状态，精确等同于参考轨迹当时状态的脚下翻色。随后使用相位 4 恢复定理，得到：

```lean
theorem delayedObstacle_standard (k : Nat) :
  StandardHighwayFrom (singleBlack (delayedObstacle k))
    (12940 + 104 * k) (-2, -2)
```

这是一族任意远、首次碰撞任意晚、且碰撞后 440 步已认证恢复的初态。恢复起点是充分时间，没有主张最早。证明中的 `k` 没有上界，也不需要为每个 `k` 重跑长模拟。

`singleBlack_no_highway_before_late_contact` 用碰撞前后相隔 104 步的读色矛盾排除过早的永久公路起点。对于上述族，所有 `T <= 12396 + 104*k` 均不可能是永久 104 步公路的起点。进一步得到此前无统一上界定理的强化版：

```lean
theorem one_black_unbounded_delay_with_recovery (N : Nat) :
  exists p : Point, EventuallyStandard (singleBlack p) ∧
    forall T, T <= N -> forall v,
      ¬HighwayFrom (singleBlack p) T 104 v
```

这次存在量词中的初态已同时证明最终恢复，不再只排除过早起点。一般的任意单黑格位置、任意多黑格配置以及进入公路前的全部混乱阶段，仍未由这些定理覆盖。

## 通用恢复证书及更多相位

`RecoveryCertificate flipTime delay origin` 要求：在标准种子运行 `flipTime` 步后翻转脚下格，接下来的 `delay` 步始终留在 `x+y <= 0` 内；末态在完整 `x+y <= weight origin` 半平面上匹配平移种子；且 `weight origin <= 0`。这三个条件只涉及一个有限前缀和入口匹配，没有预先假设无限恢复。

`RecoveryCertificate.after_blocks` 证明：只要初态 `s` 满足原始入口条件 `AgreesBelow 0 s highwaySeed`，在任意时刻 `104*k + flipTime` 翻色后，都能从第 `delay` 步开始运行标准公路。`after_entry` 再推广到任意入口时刻、方向和位置。历史长度不限，保护半平面外的棋盘颜色不限；每个结论描述一次独立翻色。

`PackedFinite.lean` 的 `packCells` 使用按位或编码列表，因此重复坐标仍代表一个黑格。`packedBoard_packCells` 和 `FiniteState.toPacked_toState` 证明编码与原始无限棋盘一致，前提是所有输入黑格都位于计算窗口内。`checkRecovery` 检查该前提，检查每一步读取前的窗口边界与半平面界限，并验证恢复入口；`checkRecovery_sound` 将成功结果转为通用恢复证书。

新增证书均由 `decide +kernel` 验证：

| 周期相位 | 从入口起的翻色时刻 | 翻色后的充分恢复时间 | 基准恢复入口 |
| --- | --- | ---: | --- |
| 5 | `1253 + 104*k = 104*(12+k) + 5` | 6645 | `(-37,-35)` |
| 66 | `66 + 104*k` | 174 | `(-4,-4)` |
| 94 | `94 + 104*k` | 238 | `(-6,-6)` |
| 95 | `95 + 104*k` | 337 | `(-6,-6)` |

表中入口是各基准恢复段末态的位置，后续周期按原公路漂移平移。所有证书返回朝北、向西南漂移的标准相位。相位 5 使用已经生成 12 个周期历史的状态，恢复路径会返回较早的历史区域；其上半平面界限经检查仍不超过 0。12 个周期是本证书采用的充分历史长度，不声称最小。

`phaseFiveObstacle_first_visit` 与 `phaseFiveObstacle_standard` 给出另一条明确单黑格族：

```text
初始唯一黑格：(-83 - 2*k, -56 - 2*k)
首次碰撞：    13333 + 104*k
永久公路起点：19978 + 104*k
```

这使用独立的相位 5 首次访问几何检查和上述 6645 步恢复证书，适用于全部自然数 `k`。以上是最初认证的六个固定相位；后续首访分类及恢复结果如下，并不声称全部 104 个相位都有统一历史恢复定理。

## 首访相位分类与 21 个相位的历史恢复

`FreshPhases.lean` 定义 `FirstVisitAt s n` 为当前格在所有 `j < n` 时刻均未被访问。对于标准种子，首访相位列表为

```text
[4, 5, 6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 66, 94, 95, 96]
```

`seed_firstVisit_iff` 对所有 `k >= 2`、`phi < 104` 证明时刻 `104*k+phi` 首访当且仅当 `phi ∈ freshPhases`。`seed_late_cell_white` 同时证明这些成熟周期中每个被读取的格子在种子初态中为白；“初始为白”不等于读取时仍白，也不单独意味着首访。综合陈述为

```lean
theorem seed_fresh_phase_classification :
    exists K0 : Nat, exists Phi : List Nat,
      forall k, K0 <= k -> forall phi, phi < 104 ->
        (FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ Phi) ∧
        highwaySeed.toState.board (run highwaySeed.toState (104 * k + phi)).pos = false
```

证明取 `K0=2`、`Phi=freshPhases`。一个周期的位置表由内核检查认证；权重范围为 `[-9,0]`，所以只需比较当前周期之前的两个周期和同周期更早相位。全部更早历史由漂移排除，结论量化无限多个 `k`。该定理针对种子历史；连接其他初态时仍需排除进入证书之前的访问。

`RotatedRecoveryCertificate` 允许恢复后转四分之一圈。有限恢复前缀和整个无限新尾部均受原权重半平面保护；新漂移的权重为零，无限尾部的权重控制来自已认证周期表及周期归纳。其延续接口为

```lean
theorem RotatedRecoveryCertificate.after_blocks {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (104 * k + f)) (run s (104 * k + f)).pos) d
      (rotatePoint r (-2, -2))
```

`FreshPhaseRecovery.lean` 的 `certifiedFreshPhases` 包含上述列表中除 6、38、49 外的 19 个相位；`certified_fresh_phase_recovers` 对每个该列表成员给出充分历史长度 `H`，之后任意 `k` 都最终恢复。`HardPhaseRecovery.lean` 再认证相位 6 和 38，得到

```lean
theorem fresh_phase_recovers_except_49 (phi : Nat)
    (hphi : phi ∈ freshPhases) (h49 : phi ≠ 49) :
    exists H : Nat, forall s : State, AgreesBelow 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos)
```

相位 6 在 `H=18` 的基准状态翻色，12611 步后转向恢复；相位 38 取 `H=13`，33148 步后同向恢复。后者路径超出原位图窗口，因此先平移 `(20,20)` 再检查。可靠性定理的精确接口为

```lean
theorem checkShiftedRecovery_sound {f d : Nat} {origin v : Point}
    (h : checkShiftedRecovery f d origin v = true) : RecoveryCertificate f d origin
```

以上结论允许原保护半平面之外存在任意颜色，包括无限历史；每个 `k` 描述一次独立翻色。它们没有认证连续多次扰动，也没有保证恢复方向始终与原公路相同。相位 49 不满足上述与历史无关的形式，由下一节单独处理。一般 `FreshObstacleStability` 还包含过渡期首次碰撞，仍未解决。

## 相位 49：平行的东北公路

有限探索曾显示，相位 49 翻色后的恢复入口对不同历史长度都落在同一绝对坐标，一度被误读为“沿遗迹返回原始区域”。逐格比较完整棋盘后确认：蚂蚁并未沿旧遗迹返回，而是在 `x-y` 约为 76 的平行位置生成朝东北的标准公路；入口坐标固定，是因为半平面证书要求新公路整个前方半平面与模板一致，必须等新公路越过旧历史之后检查才会通过。

`TrailRetrace.lean` 引入条带 `TrailStrip p :≡ -2 <= x-y <= 8`。`trail_seed_run_strip` 证明标准种子的全部未来位置都在该条带内；`trail_seed_run_white` 证明种子在条带外的格子在任意时刻都是白色。`TrailAgreement cut s t` 要求两个状态位置、朝向相同，且棋盘在 `weight <= cut` 或条带外的每个格子上相同，即只允许“条带内、权重高于 `cut`”的部分不同。

证明结构如下：

- 历史长度取 13 个周期，翻色时刻为 `trailFlipTime = 104*13+49`。为放入位图窗口，先平移 `(8,16)` 再旋转半周。`trail_prefix_check` 用 `decide +kernel` 在一次遍历中验证：52421 步前缀的每一步都在窗口内，且位于 `x+y <= 0` 或条带外；末态在完整半平面上与平移后的种子一致。整份文件的编译约需 3 分钟。
- `trail_standard` 将入口转回原坐标，得到漂移为 `(2,2)` 的标准公路。
- `trail_tail_pos` 给出尾部位置 `(39 - c.1, -37 - c.2)`，其中 `c` 是种子在对应时刻的位置。由于种子位置满足 `c.1 - c.2 ∈ [-2,8]`，尾部的 `x-y` 永远在 `[68,78]` 内。`trail_all_safe` 因此对全部时刻证明轨迹只读取 `x+y <= 0` 或条带外的格子。这是对无限尾部的证明，不是模拟。
- `seed_trail_agreement` 证明，种子多运行 `k` 个周期后的状态与平移后的基准状态满足 `TrailAgreement`。
- `StandardHighwayFrom.of_trailAgreement` 沿条带协议转移整条轨迹。

主结论为：

```lean
theorem phase_forty_nine_recovers {s : State} (h : TrailAgreement 0 s highwaySeed.toState)
    (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (104 * k + trailFlipTime)) (run s (104 * k + trailFlipTime)).pos)
      trailDelay (2, 2)

theorem all_fresh_phases_recover (phi : Nat) (hphi : phi ∈ freshPhases) :
    exists H : Nat, forall s : State, TrailAgreement 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos)
```

`all_fresh_phases_recover` 覆盖全部 22 个首访相位。它的前提 `TrailAgreement 0` 严格强于其余 21 个相位使用的 `AgreesBelow 0`：相位 49 的新公路会进入 `x+y > 0` 区域，所以这里不允许在条带外、权重为正的区域放任意颜色。这一条件对种子自身的历史成立（`phase_forty_nine_seed`），但不能自动套用到全白初态在入口之前留下的过渡期遗迹，因为那些遗迹不在条带内。每个 `k` 仍然描述一次独立翻色，不涉及连续多次扰动，也不涉及过渡期的首次碰撞。


## 任意单黑格初态

**[已证明]** `SingleBlackTheorem.lean`：

```lean
def singleBlackAt (p : Point) (d : Direction) (q : Point) : State :=
  { board := fun x => decide (x = q), pos := p, dir := d }

theorem singleBlackAt_standard (p : Point) (d : Direction) (q : Point) :
    EventuallyStandard (singleBlackAt p d q)
```

对任意蚂蚁位置 `p`、任意朝向 `d`、任意唯一黑格 `q`，蚂蚁最终运行标准 104 步公路。公理审计只依赖 `propext`、`Classical.choice`、`Quot.sound`；仓库中 2558 个 Lean 文件均不含 `sorry`、`admit`、`native_decide`、自定义 `axiom`、`unsafe`、`implemented_by` 或 `extern`。

先用旋转、平移对称性（`singleBlackAt_eq_pose`）归约到蚂蚁位于原点、朝北的 `singleBlack q`，再按全白轨迹首次访问 `q` 的时刻 `τ` 分三种情形：

1. **从不访问**：由 `perturb_standard_of_avoids`，轨迹就是全白轨迹本身。
2. **晚期访问** `τ ≥ 13952 = 12080 + 104*18`（`singleBlack_late_all`）：
   - 首次接触对应标准种子轨迹的一次首访，所以接触相位属于 22 个首访相位之一。
   - 其中 21 个相位由 `fresh_phase_recovers_late` 处理。18 是这些相位证书所需的最大历史长度（相位 6）。
   - 相位 49 单独证明，见下文。
3. **早期访问** `τ < 13952`：
   - `earlyCells_cover` 沿全白轨迹前 13952 步逐步检查，证明这段时间内访问的所有格子都属于 2215 个格子的列表 `earlyCells`。
   - `earlyCells_ok` 对其中每一个格子给出一份由内核检查的单独证书：在 256×256 窗口中运行到标准入口，并在整个半平面上与模板一致。

### 全白初态下的相位 49

在全白历史下，相位 49 的东北公路会撞上全白过渡期留下的遗迹，所以 `phase_forty_nine_recovers`（其前提是 `TrailAgreement 0`）不能直接套用。`Phase49Blank.lean` 的证明分为以下几步：

1. **`blankEntryState_eq_perturb`**：全白初态在第 12080 步的归一化状态，恰好等于种子棋盘加上 `junk49`（937 个格子，全部位于 `x+y > 0`）。这一点对全白轨迹的实际运行做内核检查。
2. **`ref49_avoids_junk`**：在对齐时刻之前，条带参考轨迹不会读到任何遗迹格。证明分两部分：
   - 前缀：每一步检查位置不落在遗迹沿对角线 `(2,2)` 方向的“阴影”上。阴影位图由定义直接构造，因此正确性不需要另外检查。
   - 东北车道：用一个有限的整数关系检查。
3. **`flip49_blank_U`**：对每个 `k`，翻色后的状态在对齐时刻都与同一个具体状态 `Y49` 在半平面 `x+y ≥ 58` 上一致。`Y49` 是东北公路第 14 周期的模板叠加上遗迹。
4. **`y49_standard`、`y49_all_U`**：`Y49` 运行 8603 步后进入朝东的标准公路（漂移 `(-2,2)`），且整个运行永远留在 `x+y ≥ 58`。其尾部的 `x+y` 落在 `[93,103]`，这一点由种子条带引理对全部时刻证明。

### 计算方式与可重现性

- 2215 个早期格子各自一份证书，参数由 `scripts/find_single_black.py` 搜索。脚本输出不被信任，全部结论由内核检查。
- 共有四种证书形式，可靠性都已证明：
  - `checkSingleBlack`：整数坐标版本；
  - `checkSingleBlackFast` 与 `checkSingleBlackFast2`：自然数位索引版本，平均快约 2 倍；
  - `SegmentCheck`：分段版本，每 12000 步写出一个字面中间状态，再用 `run_add` 链接。
- 内核在少数证书上对位索引版本出现病态的慢（例如 C0898：Fast2 用了 2194 秒，整数版本只用 25 秒）。这些证书当时改用整数版本，34 个大格子改用分段版本。
- **病态慢的原因已定位**（`FastCell3.lean`）：单步函数用 `let d := turn ...` 绑定新朝向，并在两个字段里使用它；再加上每步检查上一步的位索引，内核耗时随步数大致按指数增长（同一格子：4000 步 3.3 秒，8000 步 96 秒，18991 步超过 600 秒）。去掉 `let`、把 `turn ...` 直接写进两个字段后问题消失。`IdxState.step3` 与原单步函数定义相等（`step3_eq`），可靠性直接继承。实测 C0898 用 7.7 秒，原先超时的 76377 步大格子 C2055 用 27.9 秒，且不需要分段。机制推测为投影反复重新实例化 `let`、内核缓存无法识别；这一点未对照内核源码确认。已完成的证书不受影响，今后的大规模计算应改用 `checkSingleBlackFast3`。
- 相位 49 的 52421 步前缀检查若一次完成，会耗尽两台机器的内存（本机 8 GB 以上，远程机器的交换空间被占满）。因此拆成 13 段，每段 4000 步、单独一个模块（`Phase49K2_1` 至 `Phase49K2_13`）。
- 总计约 3300 万步内核计算，分布在本机和一台 Linux 机器上。两边使用同一 Lean 4.36.0；Linux 编译的 olean 已验证可以在 Windows 上加载，反之亦然。
- **构建注意**：`SingleBlackEarly` 与 `SingleBlackFull` 两个目标不能直接 `lake build`。Lake 会同时编译许多模块，而每个内核检查需要 1–3 GB 内存（Windows 显示的工作集约 2 GB 即被截断，实际占用更高）。应使用 `scripts/build_cells.py` 控制并发与内存。

### 边界

- 这一结论只覆盖**恰好一个**初始黑格的情形。两个及以上黑格的一般有限初态仍未证明，原始猜想 `HighwayConjecture` 也仍未证明。
- 早期格子部分是对 2215 个具体格子的有限穷举，不包含可以推广到多黑格的结构性论证。


## 周期尾部的组合归约（2026-11-21，Codex 形式化，Claude 独立复核）

`PeriodicWordCore.lean` 定义白背景自洽字 `ConsistentWord P w`：沿转向字 `w` 走一个周期后朝向回到原样，漂移 `v ≠ 0`，且在双向无限周期路径上，每一步读到的颜色等于该格此前被访问次数的奇偶。`checkConsistentWord_iff` 证明可判定检查器与命题等价。

主要结论：

```lean
theorem periodic_tail_consistent_at_start (hs : FiniteSupport s.board) (hP : 0 < P)
    (h : HighwayFrom s T P v) : ConsistentWord P (fun i => readColor s (T + i))

theorem no_odd_periodic_tail (hs : FiniteSupport s.board) (hP : 0 < P) (hodd : P % 2 = 1) :
    ¬ HighwayFrom s T P v

theorem no_periodic_tail_small (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 13) :
    ¬ HighwayFrom s T P v

theorem highwayConjecture_of_ballistic_and_consistentWordsAreStandard :
    (forall s, FiniteSupport s.board -> Ballistic s) -> ConsistentWordsAreStandard ->
      HighwayConjecture
```

- 第一条：有限支撑的周期尾部从起点 `T` 开始，读色字就已经是自洽字。
- 第二条：一般地排除奇数周期，理由是朝向回到原样要求转向数满足 `#右 − #左 ≡ 0 (mod 4)`。
- 第三条：偶数 2 至 12 用 `decide +kernel` 穷举排除。其中周期 12 拆成 8 个模块，以控制内存。
- 第四条：把原猜想归约为动力学条件 `Ballistic` 与纯组合条件 `ConsistentWordsAreStandard`。后者要求每个自洽字在循环移相后与标准字一致。

另外 `standard_word_consistent` 验证标准 104 位字本身是自洽字，作为正例检查。

### 前沿记录对（2026-11-22）

**[已证明，纯内核]** `RecordPair.lean`，公理只有 `propext`、`Classical.choice`、`Quot.sound`。

设自洽字的漂移为 `v = (a, b)`。取 `f = s₁x + s₂y`，其中 `sᵢ = ±1` 使 `f(v) = |a| + |b| > 0`。称 `n` 为记录时刻，若 `f(pos n)` 严格大于此前所有时刻的值。

- `record_pair`：在“对起点”（到达方向右转后仍使 `f` 增加的记录时刻 `m+1`），读数 `m, …, m+5` 必为 `1 0 0 0 0 1`；路径绕一个单位方格闭合（`pos(m+4) = pos m`，`pos(m+5) = pos(m+1)`）；各时刻的层依次为 `L, L+1, L, L−1, L, L−1`。
- 对起点每隔一层出现一次，相邻两个至少相隔 8 步；一个周期使首达时间恰好增加 `P`，层数增加 `f(v)`。由此得到：
  - `ConsistentWord.four_mul_driftL1_le`：`4(|a| + |b|) ≤ P`；
  - `ConsistentWord.front_factor`：每个自洽字都含循环因子 `100001`；
  - `periodic_tail_record_data`：以上两条对有限支撑轨道的周期尾部同样成立，这里的漂移是原坐标系中的漂移。
- 证明在 `prescribedBoard` 上进行（时刻 0 全白，沿重复字翻转），只使用三个事实：首次访问读白；相邻两次访问读色交替；时刻 `2P²` 之后读数与字一致。首达时间用自证的最小元引理加 `Classical.choose` 定义，不依赖 Mathlib。
- **边界**：这些都是必要条件，并且可能已被更强的已知结果覆盖，例如 Jillhewar 的 `g ≥ 2·max(|a|,|b|)`、宽度排除，以及 Ke 的 `g ≥ 8`（见 `research/related-work.md`）。`100001` 因子与 `P ≥ 4|v|₁` 在已读文献中未见，但检索并不穷尽。

### 单位对角完整漂移排除（Ke 的 `ud:thm:unit`，2026-11-22）

**[已证明，纯内核]** `UnitDiagonal.lean` 及其依赖的九个 `UnitDiagonal*` 模块，均属 `PeriodicWords` 库（`-M1536 -DwarningAsError=true`）。公理只有 `propext`、`Classical.choice`、`Quot.sound`；审计脚本为 `scripts/UnitDiagonalChecks.lean`。

```lean
theorem UnitDiagonal.no_unit_diagonal_periodic_tail' {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hv : UnitDiagonalDrift v) :
    ¬ HighwayFrom s T P v

theorem UnitDiagonal.consistentWord_not_unitDiagonal' (h : ConsistentWord P w) :
    ¬ UnitDiagonalDrift (wordDrift P w)
```

其中 `UnitDiagonalDrift v` 指完整单周期位移 `v ∈ {(±1, ±1)}`。不设周期、宽度、增长或种子大小上界，也不要求 `P` 为最小周期。

- **来源**：数学论证属于 Hao Ke（`kehao95/langtons-ant-core`，提交 `b3429c25`，`unit-diagonal.tex` 与 `unit_diagonal_analytic/PROOF.md`），本仓库的贡献仅在于 Lean 形式化。来源核验见 `research/drift-ke-source-audit-2026-11-22.md`，引理蓝图见 `research/unit-diagonal-math-blueprint-2026-11-22.md`。
- **结构**：`UnitDiagonalReduction` 用循环移位与四分之一转旋转，把轨道形式归约到字形式 `CoreUnitSE`（漂移恰为 `(1, -1)`）。核心证明定义稳定时间 `τ_i = i − P·x_i`，并说明在该漂移下 `priorPhases` 的长度就是层内稳定秩（`UnitDiagonalRank`）。关键引理有三条：首次物理返回使稳定秩恰好加一（`firstReturn_rank`）；有向端口按稳定时间保序匹配（`UnitDiagonalMatching`）；顶层唯一事件为东入、白读、南出（`UnitDiagonalExtremal`）。由此依次确定第一内层端口字为 `1000`、第二内层为 `00001101` 或 `000011010`（`UnitDiagonalWords`、`UnitDiagonalCore`）；第三内层由两次首次返回和两座禁止桥，与二元交错引理 `interleave_bridge` 矛盾（`UnitDiagonalInner`）。
- **边界**：排除的是完整位移 `(±1, ±1)`，不是约分后的方向；标准公路的完整位移 `(±2, ±2)` 不受影响。本定理只是 `ConsistentWordsAreStandard` 的一条必要排除，不解决该开放块，也不涉及 `PeriodicTail`。更大对角位移 `(±m, ±m)`（`m > 1`）的排除不能照搬本论证（见来源核验第 1 节）。

### 周期尾部的增长量：`4 ∣ g`、`g ≥ 2·max(|a|,|b|)` 与 `g = 4` 三分法（2026-11-22）

**[已证明，纯内核]** `PeriodicGrowthResidue.lean`（依赖 `DriftRank.lean` 的一般漂移稳定秩工具），公理只有 `propext`、`Classical.choice`、`Quot.sound`。

增长量 `wordGrowth P w` 定义为：在每个完整平移类中取稳定秩为 0 的相位作代表，统计访问重数为奇数的类数。已证明：

- `ConsistentWord.growth_eq_turn_balance`：`g = #R − #L`；`HighwayFrom.net_black_growth`：对有限支撑周期尾，`g` 等于每周期黑格的净增量。
- `ConsistentWord.four_dvd_growth`：`4 ∣ g`；`ConsistentWord.growth_pos`、`four_le_growth`：`g ≥ 4`。
- `ConsistentWord.two_mul_driftInf_le_growth`：`2·max(|a|,|b|) ≤ g`，其中 `(a,b)` 为完整漂移；轨道形式为 `periodic_tail_growth_bounds`。
- `ConsistentWord.growth_four_drift_trichotomy`：若 `g = 4`，完整漂移只能是单位对角、两格轴向或两格对角（共 12 个向量，`growth_four_drift_vectors`）。
- 正例检查：标准 104 步字 `g = 12`（`standard_word_growth`，经 `#R − #L` 的内核计算得到）。

- **来源**：上述结论属于 Jillhewar（Prop 5.4、Cor 6.5、Thm 7.1、Cor 7.3）与 Ke（`periodic-growth-closure.md` §2），此处只是形式化；证明采用 Ke 的显式模 4 势函数。蓝图见 `research/growth-blueprint-2026-11-22.md`。
- **边界**：结合单位对角排除，`g = 4` 只剩两格轴向与两格对角两类尚未排除；排除它们后才得到 `g ≥ 8`。所有这些都只是必要条件，不解决 `ConsistentWordsAreStandard`。

**两格轴向漂移（2026-11-22）**：`TwoCellAxial.lean`（纯内核）证明 Ke 的 Theorem B：完整漂移为 `(±2, 0)` 或 `(0, ±2)` 的自洽字满足 `P ≡ 4 (mod 8)` 且 `8 ∣ g`（`ConsistentWord.twoCellAxial_mod_eight`），因而 `g ≠ 4`（`ConsistentWord.twoCellAxial_growth_ne_four`）；轨道形式为 `periodic_tail_twoCellAxial_mod_eight` 与 `periodic_tail_twoCellAxial_growth_ne_four`。核心是运动学秩和恒等式 `K ≡ 1 + P/4 (mod 2)`，由 `PortInversion.lean` 的列表逆序分解实例化到真实后继循环得到。该定理不断言存在任何两格轴向的自洽字。

**两格对角漂移与 `g ≥ 8`（2026-11-22）**：`TwoCellDiagonalParity`、`TwoCellDiagonalGadget`、`TwoCellDiagonalRank`、`TwoCellDiagonal`（纯内核）证明两格对角完整漂移 `(±2, ±2)` 的自洽字 `g ≠ 4`，并给出 Ke 的 Theorem C：奇重数类中两种棋盘符号各至少两个（`ConsistentWord.twoCellDiagonal_checker_mixed`；标准字为 `(4, 8)` 或 `(8, 4)`，取决于相位）。`PeriodicGrowth.lean` 汇合三支排除，得到

```lean
theorem ConsistentWord.eight_le_growth (h : ConsistentWord P w) : 8 ≤ wordGrowth P w
theorem periodic_tail_eight_le_growth (hs : FiniteSupport s.board) (hP : 0 < P)
    (h : HighwayFrom s T P v) : 8 ≤ wordGrowth P (fun i => readColor s (T + i))
```

即每个有限支撑周期尾每周期的黑格净增至少为 8（Ke `periodic-growth-closure.md` 的 Theorem A，数学属于 Jillhewar 与 Ke）。审计脚本：`scripts/GrowthChecks.lean`。这仍只是必要条件，不解决 `ConsistentWordsAreStandard`。

### 对角倍数 `(m, −m)` 的通道局部引理（2026-11-22）

**[已证明，纯内核]** `DiagonalMultipleLanes.lean`。对任意 `m ≥ 1`、完整漂移 `(m, −m)` 的自洽字（**不假设最小周期**），按完整平移类（通道）分开的第一内层入射表满足：相邻通道的首次物理返回关系（`adjacent_lane_second_inner_relation`）；第一内层不能有三个连续通道的入射表同为 `1000`（`no_three_consecutive_1000`）；特例 `m = 2` 时两条通道不能都为 `1000`，`m = 1` 时该表不能为 `1000`。正例检查：旋转到 `(2, −2)` 的标准字两条通道分别为 `001` 与 `1000`。

- **来源**：纸面证明由 GPT-6 Astra 在 `research/persist-B-diagonal-m3-2026-11-22.md` 第 1、9 轮给出，是单位对角证明逐通道的推广；未见于已检索的文献（`research/prior-art-survey-2026-11-22.md`）。
- **边界**：这是局部禁型，不排除任何 `m`；排除 `m ≥ 3` 仍需全局论证（见该日志）。

### 两格对角混合尾迹的模 2 缺陷恒等式（2026-11-23）

**[已证明，纯内核]** `MixedWakeDefect.lean`。对完整漂移 `(2, −2)`、末朝向北的周期字，相邻偶层 `t, t+2`（`t` 偶）满足

```text
(eCnt(t+2, r) + nCnt(t+1, ¬r) + eCnt(t, r) + nCnt(t−1, ¬r)) mod 2
  = (classMult(t, ¬r) + classMult(t+2, r)) mod 2
```

（`mixed_step_defect`，只用精确的双通道流守恒）。标准字第 0 层的 `classMult = 3`，因此不是纯奇层尾迹（`stdHighwaySE_not_pureOddWake`），齐次情形不适用于它；另附标准字的边界接口计数（`stdHighwaySE_interfaces`，`decide +kernel`）。

- **来源**：GPT-6 Astra，第二轮 brainstorm T3（`research/brainstorm2-T3-width-2026-11-22.md` 第 2、7 节），原在仓库外临时文件中核验。
- **边界**：恒等式只依赖计数，T3 的加宽计数族同样满足它，因此它本身不给宽度上界。

### 保持有序方向表的平移与后继交换（2026-11-23）

**[已证明，纯内核]** `DirectionTableTranslation.lean`。对任意非零完整漂移 `v` 的自洽字，若空间平移 `b` 保持每个平移类按稳定秩索引的入射方向表（`PreservesTables`，所有类、所有秩，含空类），则“目标类、同秩”映射 `F` 与循环后继交换（`F_succ`）；`v = (m, −m)`、`b = (a, −a)` 时即固定层的通道平移（`diagonal_F_succ`）。零平移诱导恒等映射（`F_zero`），作为非空泛检查。

- **来源**：纸面引理为 GPT-6 Astra 第二轮 brainstorm T2（`research/brainstorm2-T2-diagonal-multiples-2026-11-22.md`），Lean 证明由 GPT-6 Astra 完成。
- **边界**：这只是 T2 排除 `m ≥ 3` 路线的第一步；由方向表对称推出单环、更短周期或矛盾的部分仍未形式化。

### 秩 0 通道：局部归约与标准字见证（2026-11-23，部分）

**[已证明，纯内核；一般定理未完成]** `DiagonalRankZeroLane.lean`。对完整漂移 `(m, −m)` 且顶层占满（`TopOccupied`）的自洽字：每个顶层类长度恰为 1；每条第一内层通道的入射表属于 `100 / 1000 / 001 / 0010`，且前两种的上入口、上出口秩为 `(0, 2)`，后两种为 `(2, 0)`（`first_inner_port_ranks`）；同类中秩 0 的稳定时间严格小于秩 2。另有纯有限求和引理 `early_of_negative_sum`。标准字（旋转到 `(2, −2)`）上验证了顶层占满、两条通道分别为 `001` 与 `1000`、端口相位与稳定时间差 `20 + (−120) = 2·2 − 104`。


**[已证明，纯内核]** `DiagonalWinding.lean` 补齐 T2 命题 1：`exists_rank_zero_lane`——完整漂移 `(m, −m)`、`m > 0`、顶层占满的任意自洽字（不假设最小周期），第一内层至少一条通道的入射表为 `100` 或 `1000`。两个中间结论：

- `strict_period_bound`：完整漂移 `(m, −m)` 的自洽字满足 `2m < P`（不需要顶层占满）。证明用单调量 `i − (x_i − y_i)`，最低层相位的北向出射使它增加 2。
- `winding_identity`：`Σ_{r<m} (τ(a_r) − τ(b_r)) = 2m − P`，其中 `a_r, b_r` 是第一内层通道 `r` 唯一的上入口与上出口相位；相邻通道经真实的 E、S 两步后继连接（位移 `(1, −1)`，不是物理返回），跨提升边界的补偿已计入。

晚入射通道（`001`、`0010`）的项为正，总和为负，故存在早入射通道。

- **来源**：纸面证明为 GPT-6 Astra 第二轮 brainstorm T2；Lean 证明由 GPT-6 Astra 完成。
- **边界**：命题 1 是局部结论，不排除任何 `m`。

### 取根与素数倍对角漂移的最小性（2026-11-23）

**[已证明，纯内核]** `RootWord.lean`。`ReadPeriod q w` 表示整个读字的周期（`ConsistentWord P w` 只约束前 `P` 项，故单独定义）。

- `root_word`：若 `ConsistentWord P w`、`0 < q`、`q ∣ P`、`ReadPeriod q w`，则 `ConsistentWord q w`，且 `wordDrift P w = (P/q) · wordDrift q w`。`q` 步恢复朝向是**推出来的**（`period_heading`：短周期的旋转须固定非零完整漂移，非恒等四分之一圈旋转只固定零向量），不需要最小性或对角性。
- `root_word_diagonal` / `least_root_diagonal`：完整漂移 `(m, −m)` 时 `P/q ∣ m`，根漂移为 `(m/(P/q), −m/(P/q))`；最小根总是存在。
- `prime_drift_minimal` / `prime_drift_least`：`m` 为素数时所选 `P` 就是最小正读周期（否则根为单位对角，被 `UnitDiagonal` 排除）。
- `odd_drift_root`：`m` 为奇数时根漂移仍为奇数且 `≥ 3`。
- 非空泛检查：标准字的 2 次幂（`P = 208`，漂移 `(4, −4)`）自洽，其 104 步根自洽且 104 是最小读周期。

- **来源**：纸面论证为 GPT-6 Astra（`research/persist-B-diagonal-m3-2026-11-22.md` 第 18 轮）；Lean 证明由 GPT-6 Astra 完成，并补出了纸面中略过的朝向恢复。
- **推论**：完整漂移为奇素数倍 `(p, −p)`（`p ≥ 3`，如 `(3, −3)`）的自洽字，所选周期已是最小读周期，直接构成目标 B 的反例；奇数倍 `m ≥ 3` 的自洽字取最小根（`least_root_diagonal`、`odd_drift_root`）后，根的倍数仍为奇数且 `≥ 3`，同样构成反例。（`m = 2` 是素数，但对应标准公路，不是反例。）目标 B 等价于：任意完整漂移 `(m, −m)` 自洽字的最小根，其漂移倍数恰为 2（单位倍数已排除）。这是纸面上的等价改写，未单列为 Lean 定理，也不是目标 B 的证明。

### `(2, −2)` 的共同时间坐标与秩间隔展开（2026-11-23）

**[已证明，纯内核]** `WidthLemmas.lean`。对完整漂移 `(2, −2)`，定义两条通道共用的时间坐标 `η(i) = 2i − P·x_i`：

- `eta_eq_stableTime`：`η = 2τ − P·(x mod 2)`，通道间偏移保留；`path_eta_difference`：任意长度的连续相位路径（可跨多个周期接缝）满足 `Δη = 2·len − P·Δx`。
- `eta_gap_ge_eight` / `adjacent_rankEta_gap`：同类相邻秩的 `η` 间隔是正的 8 的倍数。
- `boundary_rank_gap_expansion`：通道的带符号边界时间 `Σ charge·η`（向下直穿 `+1`、向上直穿 `−1`、反弹 `0`）按秩做分部求和后的精确展开，末项保留；`chargePrefix_full_eq_counts` 把末项系数还原为实际端口计数。
- 标准字数据（`decide +kernel`）：例如 `(6, true)` 秩 2→3 的间隔为 232，大于 `2·104`，说明不能假设间隔小于两个周期。

- **来源**：A 日志（`research/persist-A-width-2026-11-22.md`）第 36、37 轮，GPT-6 Astra；Lean 证明由 GPT-6 Astra 完成。
- **边界**：第 36 轮的完整切口求和式、第 33–35 轮的游程与缺陷计数仍未形式化；不给出宽度上界。

**[已证明，纯内核]** `WidthCutSum.lean` 补上第 36 轮的 (36.1)：对完整漂移 `(2, −2)` 的自洽字和任意切口 `t`，

```text
D_t = 4 · Σ_{s=t}^{T−1} f_s − P · Σ_{s=t}^{T−1} (−1)^s f_s
```

其中 `D_t` 是两通道带符号边界时间之和（`boundaryTime`，等于向下直穿与向上直穿事件的 `η` 和之差），`f_s` 是切口 `s → s+1` 的实际向上穿越数（`cutFlow`）。中间步骤 `D_t = 2·upperLength − P·upperTransport` 直接定义在上区实际边上，用周期边上的循环关联消去证明，跨周期接缝的符号全部保留，不使用 `L < P`。未构造显式的“上游程列表”对象及其与边的双射（主定理不需要它）。

**[已证明，纯内核]** `WidthDefects.lean` 补上第 33–35 轮，全部接到真实轨迹：`UpperRun` 是从层 `t` 向上出发、首次回到该层结束的真实游程（允许 `L = P`）。

- 第 34 轮 (34.1)：按端点类型 BB/BT/TB/TT 分类游程，`2(BB_t − TT_t) = f_t − f_{t−1} + A_t`（`same_colour_endpoint_defect`），`A_t` 由真实两通道重数的奇偶定义。
- 第 35 轮 (35.1)：对任意中心 `c`，`K_c = P + 4 Σ_t [(t−c) f_t + (t−c)² (BB_t − TT_t)]`（`secondMoment_defect_expansion`），不使用 `L < P`。
- 第 33 轮：BB、TT 游程不能回到同一物理格；`−2N ≤ f_t − f_{t−1} + A_t ≤ 2N`（`nonreturn_discrete_derivative_bound`）；游程与上方边一一对应（`runEdgeOccurrence_perm`），游程总长 `= 2 Σ f`，总位移 `= Σ (−1)^s f_s`（`runTransport_eq_signed_cut_sum`）。**以上三式（`runEdgeOccurrence_perm`、游程总长、`runTransport_eq_signed_cut_sum`）都需要 `botLayer ≤ t`**：切口低于整条轨迹时没有边界游程，标准字 `t = −2` 给出内核核验的反例，纸面原式未写这一条件。
- 标准字数据：`t = 4` 时 `(BB, BT, TB, TT) = (2, 3, 3, 1)`；`c = 4` 的二次矩为 168。

- **边界**：第 35 轮 (35.2) 的短游程秩方向分类未形式化；不给出宽度上界。

### `(2, −2)` 的双闭合游程分解与半漂移非对称（A 第 4 会话；2026-11-23）

**[已证明，纯内核]** `PersistA/` 下 8 个模块（GPT-6 Astra 在 A 第 4 会话中写成并核验，原样并入，仅删去 `#print`）。对任意 `P > 0`、完整漂移 `(2, −2)` 的自洽字（不假设最小周期、顶层占满、标准尾迹或增长量）：

- `PersistA.TwoGateDecomposition.exists_two_gate_decomposition`：存在四个稳定秩为 0 的锚相位（由首访前驱 `firstPred` 连成四环）和正整数 `d0, d1 < P`，使 `P = d0 + d1 + 4`，且从两个锚出发的长 `d0`、`d1` 的真实连续路径各自回到同一物理格，两段之间由真实后继（E、S 桥）连接。即：任意这类字都分解为“同格闭合游程 C0 → E,S → 同格闭合游程 C1 → E,S”。
- `PersistA.TranslationShift.no_half_drift_table_symmetry`：半漂移平移 `(1, −1)` 不可能保持全部按秩方向表（否则有半周期，其根为单位对角漂移，被排除）。
- 中间结果：首访前驱映射的类边与时钟（`FirstVisitMap`）、有限轨道必有简单环（`FiniteOrbitCycle`）、双通道商图的简单有向环在其最高层顶点处四步闭合（`TwoLaneCycle.maximal_cycle_four` / `finite_reverse_cycle_four`；结合边的定义，环长恰为 4，但该精确周期未单列为定理）、稳定时间间隔即真实闭合路径（`GatePath`）、时序回路的电压预算（`TimingCircuit`）。

- **边界**：没有限制两条游程的横向高度（标准字表明它们可在锚层两侧活动），因此不给出宽度上界。

**[已证明，纯内核]** `PersistA/SharedBoundary.lean` 形式化第 70 轮的共同边界方程：对末朝向北、完整漂移 `(2, −2)` 的字和切点 `cut ≤ P`，把相位 `[0, cut)` 记为块 U、`[cut, P)`（坐标减 `(1, −1)`）记为块 V；若 `aU`、`aV` 分别使两块内部翻色合法，则

```text
ConsistentWord P w  ⟺  对 U 访问过的 p：T_V(p+d) = a_U(p) ⊕ T_U(p+2d)，
                       对 V 访问过的 p：T_U(p+d) = a_V(p) ⊕ T_V(p+2d)，  d = (1, −1)
```

（`consistentWord_iff_sharedBoundary`；`T` 为沿 `p + 2jd` 半线的访问重数模 2，`Block.T_eq_finite_sum`）。标准字在 `cut = 90` 处两块（长 90、14）位移都为 `(1, −1)` 且满足两式。`PersistA/GateRebase.lean` 补上衔接（`exists_gate_rebase_sharedBoundary`）：任意 `(2, −2)` 自洽字在锚相位 `a0` 处循环移位后仍自洽（`cyclicShift_consistent`），切点 `d0 + 2` 处的两块恰为两段闭合游程加各自的 E、S 桥，并满足共同边界判据。由于锚点的入射朝向为南、规范轨迹从北出发，移位后的漂移为 `(−2, 2)`、块位移为 `(−1, 1)`，用的是旋转后的 `Northwest` 版本判据（同样是充要条件）。标准字实例：锚 `(16, 15, 26, 25)`、`d0 = 8`、`d1 = 92`，第二块跨周期接缝。

**[已证明，纯内核]** A 第 5 会话的 6 个模块（GPT-6 Astra，原样并入 `PersistA/`，仅删去 `#print`）：
- `ParityBand.different_tails_force_strict_interlacing`：同层同通道的两个支撑点 `a < b` 若外部需求位 `b_U = a_U + T_U(·+2d) mod 2` 不同，则另一块在开区间 `(a, b)` 内有奇数总访问（对抽象的有限站点列表陈述；接到真实字的步骤为纸面）。
- `BlockReturn.short_return_lift` / `upper_run_return_lift`：真实的同格单侧返回短于一个周期时的提升关系；`BlockMerge.cross_block_order`：跨块时钟排序与批次奇偶归并（整数与块列表层面）。
- `SharedEdge.first_return_share_direction`：真实首次返回的两端恰好共享一个入向或出向。
- `EntryBridge.first_north_read_black`：门块开始前北邻桥格刚被白读翻黑，故本块首次访问它时读黑。
- `ExtremalOverlap.other_block_above_repeat`：本块在顶层重复访问同类，迫使另一块访问更高层。
- **边界**：这些是宽度论证的局部接口；由同层交错推出横向高度界的步骤未证明，不给出宽度上界。

### `(m, −m)` 的零位移上方返回：保序与相邻禁型（2026-11-23）

**[已证明，纯内核]** `DiagonalReturnOrder.lean`。`UpperReturn` 是带完整见证的物理返回：提升后的连续路径、正长度、同格返回、中间点严格位于该格所在层之上，以及出入端口编号。对任意 `m > 0`、完整漂移 `(m, −m)` 的自洽字（不假设最小周期、不限表长）：

- `upperReturn_zeroReturn`：由首次返回秩加一，得到端口秩方程 `p[i] = q[j] + 1`。
- `upperReturn_strict_order`：同一格的零返回配对严格保序（`j < j' ↔ i < i'`），因此是单值且反向单值的部分映射。
- `upperReturn_adjacent_first`：`j → 0` 之后，下一出端口 `j+1` 的零返回只能落在入端口 1。
- `upperReturn_cycle_constant`：端口编号的有限闭链必为常值（允许不动点）。
- 标准字见证：格 `(1, 0)` 上有相位 `1 → 9`（端口 `0 → 0`）与 `9 → 85`（端口 `1 → 1`）两次真实返回，两条相邻定理的前提同时可满足。

- **来源**：B 日志第 15–17 轮，GPT-6 Astra；第 12 轮的首入射推进已在 `PortBridge.lean`（`UnitDiagonal.first_index_corollary`）中，直接复用。Lean 证明由 GPT-6 Astra 完成。
- **边界**：只排除特定端口配置，不提供跨层下降量，不排除任何 `m`。

### 上方行程的分段时序、父段分解与强制桥（2026-11-23）

**[已证明，纯内核]** `DiagonalSegments.lean`。`Excursion` 是真实的极大上方行程（两端在截面上、内部严格在上方的 `ContinuousPhasePath`），带周期平移、子段与无空隙拼接接口。对层漂移为零的非零完整漂移：

- 第 21 轮：同类事件的稳定秩比较给出 `P·(h_B − h_A) < X_B − X_A`（`Excursion.rank_edge`）；真实行程组成的任意非空比较闭路总权严格为负（`physical_cycle_weight_negative`），不要求最小周期。
- 第 23 轮：每个子段存在唯一的父段分解且覆盖完整（`exists_parentChain`、`ParentChain.unique`）；子段位移等于两次过界步加父段位移之和；零位移父段只能在链的一端（`ParentChain.zero_parent_endpoint`），非空纯零链长度恰为 2。
- 第 24 轮：零返回的强制桥两分支（`upperReturn_forced_bridge`），含零位移父段的桥环不存在，拼接保持分离，收缩后的权重为 `w + h_V − h_U`。
- 第 32 轮：同一物理竖线上的东入事件高度同奇偶（`east_entries_same_y_parity`）。
- 标准字见证：子段 `0 → 86` 的父链 `1 → 9 → 85`，两个父段位移为零、子段位移 `+1`。

- **来源**：B 日志第 21–24、32 轮，GPT-6 Astra；Lean 证明由 GPT-6 Astra 完成。
- **边界（DiagonalSegments）**：第 21 轮的反向方向（由无负环构造调度）、整周期取商后的全局父段枚举、第 24 轮五层前缀的有限搜索、第 32 轮的符号注入下界均未形式化。不排除任何 `m`。

### 全表平移缩短读周期；尾迹约束根漂移（2026-11-23）

**[已证明，纯内核]** `DiagonalTablePeriod.lean`：若通道平移 `(a, −a)`（`0 < a < m`）保持完整漂移 `(m, −m)` 自洽字的全部按秩方向表，则诱导映射是循环移位 `i ↦ (F 0 + i) mod P`，`F 0` 是周期延拓的读周期且 `0 < F 0 < P`，故 `P` 不是最小读周期（`diagonal_tables_not_least`）。**这种平移的存在性没有证明**。

**[已证明，纯内核]** `RootTail.lean`：周期算术。若最小周期为 `P` 的序列最终有周期 `q`，则 `P ≤ q`；在同一前提下（`q > 0`），若坐标 `x` 每 `P` 步前进 `m`、最终每 `q` 步前进 `u ≥ 0`，则 `m ≤ u`；`u = 2`、`m ≥ 2` 时 `m = 2` 且 `P = q`（`tail_two_exact_root`）。引理对任意整数坐标成立，用于真实轨迹时取其横坐标。

- **来源**：B 日志第 4 会话（GPT-6 Astra）的仓库外草稿，原样并入。

**[已证明，纯内核]** `FrontierCollision.lean`（B 第 6 会话草稿，原样并入）：区域内状态一致沿运行保持（`RegionEq.run`）；正时间后的前沿状态碰撞使整个未来平移（`region_shift_future`）；若碰撞的横向平移 `0 ≤ a < m` 小于完整漂移，则所选周期不是最小读周期（`frontier_collision_not_least`）；删去永不再读的格不改变轨迹（`trimFuture_trace`）；首次读取决定初始颜色（`initial_color_forced`）。**真实字中碰撞的存在性没有证明。**

### 有限支撑轨道的黑格数下界（C 第 3 轮；2026-11-23）

**[已证明，纯内核]** `BlackCountBound.lean`。对任意有限状态（黑格列表无重复）、窗口宽 `W > 0`：

- `cache_balance` / `cache_balance_interval`：最近窗口缓存的精确单步与区间收支 `A(n+1) − A(n) = 1 − 2c(n) + m(n) − e(n)`（失配 `m`、淘汰 `e`）；淘汰至多一格且只能是窗口最早的读格。
- `black_cache_balance`：完整黑格数 `B(a+L) − B(a) = A(a+L) − A(a) + 淘汰数 − 失配数`。
- `black_bound_of_event_bound`：**条件归约**——若事件数 `失配 + 淘汰 ≥ K`，则 `B(a+N) ≥ B(a) − W + K − 2·失配`。
- `finite_highway_growthInt_ge_eight`：有限支撑的真实 `HighwayFrom` 每周期带符号增长至少 8。

- **[已证明，纯内核] 无条件不等式** `BlackCountBound2.lean`：对任意有限支撑初态、`W ≥ 1`、`N ≥ W`，

  ```text
  |B_N| ≥ |B_W| − W + ⌊(N − W) / 2^W⌋ − 2·E_W(N)
  ```

  其中 `E_W(N)` 是时刻 `W..N−1` 中“黑读且所读格不在最近 `W` 步读过的格中”的次数（`missCount`）。`black_bound_finiteSupport` 对任意无重复的精确黑格枚举成立。证明：无事件（无失配、无黑格淘汰）区间上，窗口缓存本身按真实蚂蚁规则演化（`cacheState_run`）；相同的长 `W` 读色后缀使缓存相差一个刚体运动（`cacheState_rigid_of_suffix`）；有限棋盘不能在正时间后回到自身的刚体像（`finite_no_rigid_return`：迭代四次得平移回返，即零净增长的有限支撑公路，与增长 ≥ 8 矛盾）。故每 `2^W` 步至少一个事件（`event_bound_suffix`，此步对任意初态成立），再代入缓存收支。状态数确为 `2^W`：后缀只决定缓存到刚体运动，不需要朝向因子。
- **来源**：纸面论证为 GPT-6 Astra（`research/persist-C-periodic-tail-2026-11-23.md` 第 3 轮）；Lean 证明由 GPT-6 Astra 完成，用刚体回返直接排除重复后缀，绕开了纸面的“抽象预测器循环”。
- **边界**：这不证明窗口外黑读稀疏（C-M），也不证明最终周期性。

### 方向进度预算（C 第 2 会话；2026-11-23）

**[已证明，纯内核]** `DirectionalBudget.lean`。对任意有限状态、任意每步变化不超过 1 的整数投影 `f`（`UnitProjection`，如 `f(x, y) = x`）和块长 `L ≥ 1`，令 `h_k = f(p_{kL})`、`d_k = max(0, 1 − (h_{k+1} − h_k))`、`D_K = Σ_{k<K} d_k`、`W = L(4L + 2)`：

```text
E_W(N) ≤ |B_0| + 2L · D_{⌈N/L⌉}
```

（`directional_budget`；`E_W(N) = missCount s W W (N − W)`，`|B_0|` 为初始黑格集的实际基数）。另有从时间 0 统计全部失配的更强版本。推论 `sublinear_of_defect`：若某个固定方向与尺度上 `D_K = o(K)`，则 `E_W(N) = o(N)`（`o(·)` 以“对每个 `q > 0` 最终 `q·a(N) ≤ N`”表述）。

- **来源**：纸面论证为 GPT-6 Astra（C 日志第 2 会话）；Lean 证明由 GPT-6 Astra 完成，审读未发现需要加强的假设。
- **边界**：没有证明一般有限初态存在使 `D_K = o(K)` 的方向与尺度；该前提即使成立，也只推出 C-M。

**[已证明，纯内核]** `TimeReversal.lean`、`PeriodicFlux.lean`（C 第 2 会话草稿，GPT-6 Astra；由 DeepSeek V4.1 Flash 并入，仅改命名空间与一处 linter 选项，证明未改）：完整状态时间反演 `reverseC` 是对合、把一步前进共轭为一步后退、保持有限支撑，反演后的运行按逆序读出补色（`read_reverseC_run`）；`axisParity` 沿运行守恒而反演必翻转它，故任何运行状态都不等于自身某状态的反演，也不等于其偶平移，连位姿相同都不可能（`run_pose_ne_translate_reverseC_C`）。仓库已有的 44 步背景字增长为 12、黑输入相位恰为 7 个，有背景实现却不是白背景自洽字（`mixed44_positive_growth_not_white_C`）：正增长加背景实现推不出白背景自洽。

### 扩展到周期 ≤ 35（P = 34 的块在 Kaggle 上计算）

**[已证明，信任基础进一步扩大]** `PeriodicNative/Small35.lean`：

```lean
theorem no_periodic_tail_native35 (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 35) :
    ¬ HighwayFrom s T P v
```

- **块的计算**：P = 34 的 1024 个块（`PeriodicNative/P34B*.lean`，`fastScan 34 2^24 (2^24·k)`）由 Kaggle 云端的 CPU 实例计算。
  - 环境：Linux 版 Lean 4.36.0 工具链；源文件与 commit `bbe6e53` 一致，运行前在云端逐个校验了 SHA-256。
  - 结果：1024 块全部通过、0 失败，用时约 6.5 小时。
  - 记录：日志、汇总与 1024 个 olean 的 SHA-256 存于 `data/periodic-native/`。
- **装配方式**：olean 下载后放入 `.lake/build/lib/lean/PeriodicNative/`，在本机用 `lean` 直接编译 `All34.lean` 与 `Small35.lean`。不要对 `PeriodicNative.P34B*` 运行 `lake build`，否则会在本机重算（约 20 核时）。
- **信任基础**：除 `Small.lean` 已有的部分外，又增加了 1024 个 `native_decide` 公理。这些公理由 Kaggle 上运行的 Lean 编译器与原生代码产生，因此还需要信任该机器如实执行了计算。任何人都可以按 `scripts/kaggle_make_kernel.py` 或 `scripts/gen_periodic_native.py` 重算。
- **公理审计**：`propext`、`Classical.choice`、`Quot.sound`，加上 1385 个 `*._native.native_decide.ax_*`，没有其他公理。
- **与已有工作的关系**：Jillhewar 的预印本已用非形式化的穷举排除了周期 ≤ 48（见 `research/related-work.md`），因此本结果的意义仅在于它是 Lean 检查的。

### 任意漂移的周期尾部是弹道的（2026-11-21）

**[已证明，纯内核]** `BallisticGeneral.lean`：`HighwayFrom.ballisticFrom_of_pos` 对任意正周期、任意（必然非零的）漂移给出显式弹道常数（速度 `|v|²/P`，回退界 `P·|v|₁+|v|²`）。由此，有限支撑下 `Ballistic s ↔ PeriodicTail s ↔ EventuallyBoundedMemory s`，并且

```lean
theorem highwayConjecture_iff_periodicTail_and_consistentWordsAreStandard :
    HighwayConjecture ↔
      (∀ s, FiniteSupport s.board → PeriodicTail s) ∧ ConsistentWordsAreStandard
```

这只是第一个开放块的等价改写（“每个有限轨道最终沿平移重复”），并未削弱它。多代理调研得到的候选引理与文献结论见 `research/open-blocks-survey.md`。

### 扩展到周期 ≤ 33（使用 `native_decide`，2026-11-21 经用户批准）

**[已证明，信任基础扩大]** `PeriodicNative/Small.lean`：

```lean
theorem no_periodic_tail_native (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 33) :
    ¬ HighwayFrom s T P v
```

有限支撑状态不可能最终以周期 `P ≤ 33` 做周期运动。

- **周期的覆盖方式**：偶数 2 至 12 沿用纯内核检查；偶数 14 至 32 由 `native_decide` 穷举，拆成 361 个块模块、在本机并行构建（P = 28 至 32 共约 62 分钟）；奇数周期由一般证明排除。
- **快速检查器**：`PeriodicWordFast.lean` 的 `fastCheck` 把路径一次算入数组，`fastCheck_eq` 证明它与 `checkConsistentWord` 相等；`checkNoWords_of_fastBlocks` 把各块的扫描拼接起来。该模块用 `precompileModules = true` 编译为本机动态库（`PeriodicFastLib`），比解释执行快约 13 倍。
- **信任基础**：除 `propext`、`Classical.choice`、`Quot.sound` 之外，还依赖 361 个 `native_decide` 公理（`*._native.native_decide.ax_*`），即 Lean 编译器与原生执行的正确性。纯内核结论 `no_periodic_tail_small`（`P ≤ 13`）保持不变，公理仍只有标准三个；单黑格定理等其他结论也不受影响。

**边界。**

- `ConsistentWordsAreStandard` 与 `Ballistic` 都未证明，原猜想仍未解决。
- 探索程序 `scripts/periodic_words.c` 的有限枚举显示，偶数 `P ≤ 32` 内没有自洽字。这只是探索结果，不进入证明。

## 自洽字的有限初态实现与双向归约（2026-11-21，Codex）

`PeriodicWordRealizationTrace.lean` 和 `PeriodicWordRealization.lean` 补齐逆向：每个正长度的白背景自洽字，都能由显式构造的有限黑格初态实现，且从初始时刻起就具有指定读色和周期漂移。

```lean
theorem ConsistentWord.realizable (h : ConsistentWord P w) (hP : 0 < P) :
    exists s : State, FiniteSupport s.board ∧ HighwayFrom s 0 P (wordDrift P w) ∧
      forall n, readColor s n = w (n % P)

theorem consistentWord_iff_finite_realization (hP : 0 < P) :
    ConsistentWord P w ↔
      exists s : State, FiniteSupport s.board ∧ HighwayFrom s 0 P (wordDrift P w) ∧
        forall n, readColor s n = w (n % P)

theorem periodicIsStandard_iff_consistentWordsAreStandard :
    PeriodicIsStandard ↔ ConsistentWordsAreStandard

theorem highwayConjecture_iff_ballistic_and_consistentWordsAreStandard :
    HighwayConjecture ↔
      (forall s : State, FiniteSupport s.board -> Ballistic s) ∧ ConsistentWordsAreStandard
```

构造 `wordRealization P w`：先按 `repeatWord P w` 指定的转向走 `2*P` 个周期，在全白棋盘上翻转每个经过的格子，然后把所得棋盘及终点位姿作为初态。构造前缀只是辅助路径，不假定其读色符合蚂蚁规则，也不声称它是从全白初态出发的实际运行。

`repeatWord_visits_phase_perm` 证明，周期编号达到 `2*P` 后，每个相位的全部先前访问按模 `P` 映射，恰为 `priorPhases` 的一个排列。非零漂移保证固定相位不会重复计数；已有重叠界保证更早的访问没有遗漏。结合翻色奇偶及自洽条件，后续每一步都服从真实蚂蚁规则，得到完整无限运行定理 `ConsistentWord.realization_run`。

`wordRealization_support_bound` 给出长度为 `2*P*P` 的列表覆盖初态所有黑格，即黑格数量至多 `2*P^2`；列表可含重复，不声称恰有这么多黑格。初态的位置由构造给出，不强行设为原点。字在前 `P` 位之外的值完全不参与构造。

因此组合分类条件与 `PeriodicIsStandard` 已经等价。如果存在违反该分类条件的自洽字，构造立即给出有限支撑的非标准周期反例；不再存在“自洽字可能无法由有限初态实现”的缺口。所有自洽字的分类及所有有限初态的 `Ballistic` 仍未证明，主猜想仍未解决。此扩展采用符号证明，不使用 `native_decide` 或新的枚举证书。

## 任意数量且逐个被访问的初始黑格

`MultipleObstacles.lean` 定义 `multipleObstacles n`：蚂蚁从原点朝北，初始黑格恰为

```text
{ (-68 - 8*i, -42 - 8*i) | 0 <= i < n }
```

其余格子全白。所有障碍都在时刻零放置；没有在运行过程中新增、删除或移动障碍。`multipleObstacles_black` 给出该集合与棋盘函数的精确等价关系，`multipleObstacles_finite` 证明有限支撑。坐标随 `i` 严格变化，因此此状态具有恰好 `n` 个初始黑格。

主结果为：

```lean
theorem multipleObstacles_standard (n : Nat) :
  StandardHighwayFrom (multipleObstacles n)
    (12496 + 548 * n) (-2, -2)

theorem multipleObstacles_visits (n i : Nat) (hi : i < n) :
  (run (multipleObstacles n) (12604 + 548 * i)).pos =
    (-68 - 8 * (i : Int), -42 - 8 * (i : Int))
```

另有 `multipleObstacles_first_visits`，排除该格在 `12604 + 548*i` 之前的全部访问。因此每个初始黑格都实际被遇到，并且已证明它们按列表顺序首次被访问。`n` 没有上界；最终公路起点是充分时间，没有主张最早。

证明的基本转移在 `ObstacleChain.lean` 中：标准入口前方的第一格障碍位于 `(-4,-4)`，剩余障碍位于 `(-12,-12), (-20,-20), ...`。内核验证带首个障碍的 548 步前缀始终满足 `-23 <= x+y <= 0`，并在 `(-8,-8)` 重新进入标准公路，保护边界为 `x+y <= -16`。剩余障碍均满足 `x+y <= -24`，所以这段前缀无法读取它们。

`AgreesBelow.run_perturb` 在有限前缀中携带固定扰动掩码，保留全部已生成历史；它把上述范围界限转为“剩余障碍仍未参与运行”的精确状态关系。重新平移坐标后，剩余配置恰好具有相同形式且障碍数减一。`chain_step` 证明这一转移，`chain_standard` 对障碍数归纳，`chain_first_visits` 则对每个障碍的首次访问时间归纳。

连接全白初态时，先证明所有这些障碍在第 12496 步以前都不会被访问：前 12080 步使用经过认证的窗口边界，后续部分使用标准公路的首次访问几何。时刻 12496 的入口位于 `(-64,-38)`。从该入口起，每次转移耗时 548 步，且其中第 108 步首次读取当前障碍，第 548 步接回下一入口。

这覆盖了数量任意、会发生连续碰撞的有限黑格配置，但要求明确的排列和间距。它没有证明任意间距、任意二维位置或彼此干扰的任意有限黑格初态最终进入公路。归纳中减少的是这类构造里尚未读取的初始障碍数量；没有声称任意运行中的黑格总数单调减少。

## 无限障碍链的非标准 548 步公路

把有限初态族的障碍数量去掉上界，定义 `infiniteObstacles`，初始黑格恰为

```text
{ (-68 - 8*i, -42 - 8*i) | i : Nat }
```

蚂蚁仍从原点朝北，除该单向无限链外全部为白格，不添加任何有限公路种子。`infiniteObstacles_black` 证明上述集合描述与棋盘函数完全一致。运行到第 12496 步后，它进入新的周期运动：

```lean
theorem infiniteObstacles_highway :
  HighwayFrom infiniteObstacles 12496 548 (-8, -8)
```

对所有 `t >= 12496`，位置满足 `pos(t+548) = pos(t)+(-8,-8)`、朝向相同；读色也每 548 步重复。`12496` 是已证明的充分起点，没有主张最早。这里的周期是位置的平移重复、朝向和读色重复，不要求含全部历史遗迹的整张棋盘全局平移相等。

证明直接在无限棋盘上完成，并非从“所有有限 n 都最终进入标准公路”交换极限得到。先在归一化坐标中定义无限掩码 `M = {(-4-8*i,-4-8*i) | i : Nat}`。它可精确分解为当前首个障碍和向 `(-8,-8)` 平移的同一无限掩码。首段 548 步只读取 `-23 <= x+y <= 0`，剩余无限尾部满足 `x+y <= -24`，因此仍可套用固定掩码耦合。

第 548 步，整个前方 `x+y <= -16` 半平面与平移后的初始无限状态一致。于是得到真正的 `HighwayCertificate infiniteChainSeed 548 (-8,-8) 0`；通用证书归纳证明无限延续。无限初态进入该归一化状态的前缀也已证明，故不需假设其最初已经处于公路状态。

`infiniteObstacles_not_finite` 证明这个初态没有有限支撑。`infiniteObstacles_no_period104` 进一步对任意起点 `T` 和任意整数位移 `v` 排除 `HighwayFrom infiniteObstacles T 104 v`。其理由已形式化为周期平均速度相容性：同一轨迹若有周期 `P,Q`、位移 `v,w`，则必须满足 `Q*v.x = P*w.x`。本例要求 `104*(-8) = 548*w.x`，不存在整数解。因此即使允许等待任意久，它也不能最终变成标准公路；这不构成有限支撑猜想的反例。

## 最小周期与有限链极限

`InfiniteHighwayPeriod.lean` 从已认证的单障碍 548 步前缀构造读色字，证明它等于无限公路的一整个周期。`obstacleWord_no_short_period` 用内核计算排除所有 `1 <= q < 548`：每个候选都存在某个 `j < 109`，使周期字的第 `j` 位与第 `(j+q) mod 548` 位不同。

`infiniteObstacles_minimal_read_period` 因此排除更短的正读色周期。`infiniteObstacles_no_short_tail` 再利用 548 周期性把任何有限见证平移到任意晚时刻，排除任意 `T`、任意 `0 < q < 548`、任意整数位移的最终平移公路。因而 548 也是包含朝向的平移运动的最小最终正周期，而非仅一个可用的非最小周期。

`InfiniteChainLimit.lean` 给出精确的有限观察意义下收敛：对任意观察界限 `N`，保留 `n >= N` 个障碍足以使两条轨迹在全部 `j <= N` 的位置、朝向和读色完全相同。`n >= N` 只是简单的充分条件，未优化。证明利用每步横坐标至多减少 1，以及有限和无限棋盘在可达区域中的初始颜色一致；它不要求整个棋盘相等。

```lean
theorem finiteChains_match_infinite_prefix (N n : Nat) (hn : N <= n) :
  forall j, j <= N ->
    (run (multipleObstacles n) j).pos = (run infiniteObstacles j).pos ∧
    (run (multipleObstacles n) j).dir = (run infiniteObstacles j).dir ∧
    readColor (multipleObstacles n) j = readColor infiniteObstacles j
```

所有有限链都已证明最终运行标准 104 步公路，无限链则永远不能最终运行标准公路。两者相容：有限链的证明在处理完最后一个障碍后给出永久标准公路，充分恢复时间 `12496 + 548*n` 随 `n` 增大而增大；无限链没有最后一个障碍。逐个有限时间窗口的一致，并不保证存在一个对所有 `n` 通用的“此后永远标准”的起点。

## 任意偶数间距的无限公路族

`spacedObstacles k` 的蚂蚁初始位置为原点、朝北，初始黑格恰为

```text
{ (-68 - (8+2*k)*i, -42 - (8+2*k)*i) | i : Nat }
```

其余格子全白，全部障碍在初始时刻已存在。`spacedObstacles_black` 给出精确颜色描述，`spacedObstacles_not_finite` 对任意 `k` 证明无限支撑。`spacedObstacles_zero` 证明 `k=0` 时整个初始状态等于先前的 `infiniteObstacles`，不只是周期相同。

令 `P(k)=548+104*k`、`v(k)=(-8-2*k,-8-2*k)`。已证明：

```lean
theorem spacedObstacles_highway (k : Nat) :
  HighwayFrom (spacedObstacles k) 12496 (spacedPeriod k) (spacedShift k)
```

因此对所有 `t >= 12496`，位置满足 `pos(t+P(k))=pos(t)+v(k)`，朝向相同。`spacedObstacles_reads` 另证明完整读色尾部以同一周期重复。12496 是充分进入时刻，不声称最早；周期依然指轨迹的平移重复，不要求整张历史棋盘全局平移相等。

| 参数 `k` | 相邻黑格的坐标差绝对值 | 精确最小最终正周期 | 位移 |
| ---: | ---: | ---: | --- |
| 0 | 8 | 548 | `(-8,-8)` |
| 1 | 10 | 652 | `(-10,-10)` |
| 2 | 12 | 756 | `(-12,-12)` |
| 10 | 28 | 1588 | `(-28,-28)` |

归一化的首个障碍始终位于 `(-4,-4)`。首段沿用已认证的 548 步碰撞恢复，平移 `(-8,-8)`。随后继续运行 `k` 个标准 104 步周期，增加位移 `(-2*k,-2*k)`。合计恰好是 `P(k)` 和 `v(k)`，下一个障碍的相对位置再次成为 `(-4,-4)`。

拼接所需的非干扰条件有独立证明。`standard_diagonal_lower_bound` 表明：标准种子在时刻 `n` 若位于对角线，其横坐标严格大于 `-4-2*(n/104)`。因此 `spacedTail_avoids_standard` 排除追加的 `104*k` 步提前读取后续障碍。`spaced_standard_prefix` 携带剩余无限掩码及完整历史，`spaced_certificate` 在整个前方半平面上验证一次重启条件；无限延续由通用公路证书推出。参数 `k` 不需要有界枚举或额外长模拟。

`spaced_speeds_injective` 证明：若两个参数的周期和位移满足相同平均速度的交叉乘积等式，则参数必相等。因而这些成员不能通过平移或改选周期相位变为同一种平均速度。`spacedObstacles_no_period104` 对每个 `k`、任意时刻 `T` 和任意整数位移 `v` 排除 `HighwayFrom (spacedObstacles k) T 104 v`，不限于标准的四个对角位移。

进一步，周期和横向位移满足整数恒等式

```text
P(k) + 52*v(k).x = 132
```

若同一轨迹还有最终正周期 `Q`、整数位移 `w`，平均速度相容性给出 `Q*v(k).x=P(k)*w.x`，从而

```text
P(k) * (Q + 52*w.x) = 132*Q
```

右侧严格为正，括号内是正整数，因此 `P(k) <= 132*Q`。这就是 `spacedObstacles_period_lower_bound`。`spacedObstacles_unbounded_periods B` 选取 `k=2*B`，同时给出该成员的已认证正周期，以及对任意起点、任意位移、所有 `1 <= Q <= B` 的最终公路排除。因此最小最终正周期没有统一上界；这比仅列出越来越大的非最小周期更强。

上述速度论证给出初步下界；下面的读色标记证明进一步确定每个 `k` 的精确最小周期就是 `P(k)`。一般掩码使用经典可判定性定义存在自然数索引的成员关系，标记为 `noncomputable`；这用于描述无限棋盘，不是把运行或公路结论设为公理。

等距无限链定理不反驳有限支撑猜想，也没有解决任意有限二维排列的恢复问题。下面的独立间距构造进一步推广有限链恢复与有限观察极限，允许每段分别取任意不小于 8 的偶数间距。

## 精确最小周期与全部最终周期

`spacedColor k` 定义一个明确的周期字：先是已认证的 548 位碰撞字，再拼接 `k` 个标准 104 位字，然后按 `P(k)=548+104*k` 取模重复。`spacedSeed_exact_reads` 和 `spacedObstacles_exact_reads` 证明这个组合字等于实际无限棋盘的完整读色尾部，不把模拟结果当作无限周期性的前提。

关键标记为六次读色 `LLRLLL`，其中 `L=true` 表示读黑左转，`R=false` 表示读白右转。Lean 内核验证：

- 在 548 位碰撞字的循环中，标记只从偏移 107 开始。
- 在碰撞字加一个标准字形成的 652 位循环中，标记仍只从偏移 107 开始。
- 在标准 104 位字的循环中，标记不出现。

`collisionMarker_unique_in_period` 对任意 `k` 分类六位窗口的位置：碰撞段内及其出口连接处对应 652 位检查；标准段内部归约到标准字；最后五个位置跨越下一碰撞段的边界，对应 652 位字末尾；`k=0` 由 548 位检查覆盖。因此无论插入多少个标准周期，标记都只在同一个余数类出现。

实际运行上的精确结果为：

```lean
theorem spacedObstacles_marker_iff (k n : Nat) :
  HasCollisionMarker
    (fun j => readColor (spacedObstacles k) (12496 + j)) n ↔
      n % spacedPeriod k = 107
```

也就是说，已认证尾部中的标记起点恰为 `12603 + P(k)*m`。这个偏移是六位标记的起点，不是首个障碍的首次访问时刻。

若读色在任意更晚时刻开始以 `Q` 为周期，选择该时刻之后的一个标记起点；平移 `Q` 后仍须为标记起点。两个起点均在模 `P(k)` 的 107 类，故 `P(k)` 整除 `Q`。`spacedObstacles_read_period_dvd` 对任意最终起点证明这一结论；再用 `HighwayFrom.reads_periodic` 得到公路运动的周期整除关系。这里没有只排除“从第 12496 步开始”的短周期，也排除了通过丢弃任意长前缀而获得短周期的可能。

`spacedObstacles_exact_minimal_period` 同时给出周期 `P(k)` 的存在和所有更短最终正周期的排除。`spacedObstacles_read_period_iff` 进一步证明最终读色周期恰好是 `P(k)` 的倍数。通用定理 `HighwayFrom.multiple` 把任意公路延续为其整数倍周期，配合一个时刻的位置比较，得到完整分类：

```lean
theorem spacedObstacles_highway_iff (k Q : Nat) (w : Point) :
  (exists T, HighwayFrom (spacedObstacles k) T Q w) ↔
    exists m : Nat,
      Q = spacedPeriod k * m ∧ w = offset (spacedShift k) m
```

其中 `offset v m` 是 `m` 次相加，即位移 `m*v`。该定理包含形式上平凡的 `Q=0,w=(0,0)`；限制正周期时，恰有 `m>=1`。例如间距 10 的成员精确最小周期是 652，周期 1304 必须配位移 `(-20,-20)`，不可能仍配 `(-10,-10)`。

有限检查采用经过证明等价的布尔检查器与位编码。548 位字面表经 `checkTrace` 与真实有限运行逐项核验，再分别核验碰撞字、标准字的位编码；标记检查使用这些编码减少内核中的重复展开。`checkMarkerLocations_sound` 和 `markerAt_iff` 把布尔结果还原为原始六位窗口命题。全部计算证书仍使用 `decide +kernel`，没有使用 `native_decide`，探索脚本不进入证明依赖。

## 间距独立选择的有限链恢复

设有限列表 `ks=[k_0,...,k_(n-2)]`，其中每个参数都是自然数。定义 `n=ks.length+1` 个初始黑格，首格固定为 `p_0=(-68,-42)`，之后

```text
p_(i+1) = p_i + (-8-2*k_i, -8-2*k_i)
```

全部黑格在初始时刻放置，蚂蚁从原点朝北，其余格子全白。空参数列表表示一个障碍，零障碍情形仍由全白初态定理覆盖。`variableCells_length` 和 `variableCells_distinct` 分别证明列表长度与无重复坐标；`variableObstacles_black` 给出精确黑格集合，`variableObstacles_finite` 证明有限支撑。

`variableObstacles_standard` 证明充分恢复时刻

```text
12496 + 548*n + 104*sum(ks)
```

之后永久运行标准 104 步公路，位移为 `(-2,-2)`。这里没有主张恢复时刻最早。参数数量、各个参数大小以及它们的排列都没有上界；仅要求这条特定对角线和偶数间距至少 8。

例如 `ks=[0,3,1]` 给出黑格 `(-68,-42),(-76,-50),(-90,-64),(-100,-74)`，相邻间距分别为 8、14、10，已证明从第 15104 步起永久标准。

通用拼接定理使用 `AheadMask mask`：所有掩码黑格位于 `(-4-2*i,-4-2*i)`，其中 `i` 为自然数，允许有限或无限集合。`prependObstacles k mask` 在当前 `(-4,-4)` 放置首个障碍，把剩余掩码整体平移 `(-8-2*k,-8-2*k)`。548 步碰撞前缀不会读取剩余掩码；随后 `104*k` 步标准前缀也不会读取它。`variableBlock_entry` 在完整前方半平面上返回平移后的剩余模板，保留所有已生成历史。有限链恢复由这一个转移对列表归纳得到，未为每个列表执行新的模拟。

## 任意无限间距序列与非周期轨迹

令 `f : Nat -> Nat` 指定每段参数，定义

```text
D_0 = 0,  D_(i+1) = D_i + 4 + f(i)
T_0 = 0,  T_(i+1) = T_i + 548 + 104*f(i)
```

初始黑格恰为 `p_i=(-68-2*D_i,-42-2*D_i)`。`scheduledObstacles_black` 证明集合描述，`scheduledObstacles_not_finite` 证明对所有 `f` 都是无限支撑。蚂蚁仍从原点朝北出发，不添加有限公路种子，不在运行过程中插入障碍。

`scheduledObstacles_entries` 对每个 `i` 证明时刻 `12496+T_i` 的完整前方半平面匹配下一个未处理的无限尾部。该段的前 548 次读色是固定碰撞字，接着的 `104*f(i)` 次读色是标准字的重复。`scheduledObstacles_visits` 证明在 `12604+T_i` 访问初始障碍 `p_i`；后续的 `scheduledObstacles_first_visits` 进一步排除了所有更早访问。

以下条件足以排除所有最终正周期：

```lean
forall N B : Nat, exists n, N <= n ∧ B <= f n
```

它要求在任意晚的下标之后仍有任意大的间距参数，不要求 `f` 单调。`scheduledObstacles_no_read_period` 对任意起点 `T` 和正整数 `Q` 排除最终 `Q` 周期的读色；`scheduledObstacles_no_highway` 因而排除任意整数位移的最终平移公路。此处没有证明任意非周期但有界的参数序列都产生非周期运动。

证明继续使用六位字 `LLRLLL`。每个碰撞段在偏移 107 出现该标记，而标准字的任何相位都没有这个标记。假设有最终周期 `Q`，选择足够晚且 `f(i)>=Q+1` 的一段。从该段已知标记起点向后平移 `Q*(441/Q+1)` 步，仍应出现标记。由于 `441=548-107`，新标记恰好落在标准段开头之后的第 1 到第 `Q` 个位置，完整六位窗口仍在标准段内，与无标记结论矛盾。这给出无限时间结论，不依赖有限模拟未发现周期。

取最简单的 `f(i)=i`，相邻间距依次为 8、10、12、14 等。`growingObstacles_black` 证明显式坐标

```text
p_i = (-68-i*(i+7), -42-i*(i+7))
```

前五个黑格为 `(-68,-42),(-76,-50),(-86,-60),(-98,-72),(-112,-86)`。`growingObstacles_no_highway T Q hQ v` 对任意 `T`、正 `Q` 和位移 `v` 排除公路；`growingObstacles_no_read_period` 排除读色最终周期；无限支撑及不最终标准也有单独定理。

## 非周期无限链的有限截断

`schedulePrefix f n` 保留前 `n` 个间距参数，因而保留黑格 `p_0,...,p_n` 共 `n+1` 个。`finiteSchedule_black` 证明这个截断描述；`finiteSchedule_standard` 证明它从 `13044+T_n` 起永久运行标准 104 步公路。

对递增间距例子，`growing_time_formula` 给出

```text
T_n = 52*n*(n+7) + 132*n
```

所以前 `n+1` 个黑格的充分恢复起点为 `13044+52*n*(n+7)+132*n`。例如保留前四个黑格，已证明从第 15000 步起永久标准；完整无限链则没有任何最终正周期。

`finiteSchedules_match_infinite_prefix` 对任意 `f` 证明：给定观察时长 `N`，只要保留 `n+1` 个障碍且 `n>=N`，有限和无限轨迹在每个 `j<=N` 的位置、朝向、读色完全相同。该保留数量只是简单的充分条件，没有优化。证明使用每步横坐标至多减少 1，以及上述坐标在每个有限可达区域中的初始颜色一致。

因此现在既有有限标准轨迹逼近非标准周期轨迹的例子，也有有限标准轨迹逼近永不最终周期轨迹的例子。有限观察窗口的一致不足以传递“此后永远标准”这一性质。无限例子始终不满足有限支撑，不构成原始有限支撑猜想的反例。

## 首次接触与精确恢复起点

`finiteSchedule_first_visits f n i hi` 对每个 `i<=n` 同时证明时刻 `12604+T_i` 到达 `p_i`，以及每个更早时刻的位置均不为 `p_i`。归纳使用两个事实：当前块的首个障碍在偏移 108 首次接触；整个 `548+104*f(i)` 步模块都不读取剩余障碍。全白初始前缀的避障论证把归一化结果还原到初始时刻。无限链的首次访问结论由足够长有限截断与无限轨迹的精确耦合得到。

最后一个障碍的首次接触时刻记为 `C_n=12604+T_n`。`finiteSchedule_highway_start_lower_bound` 对任意正周期 `Q` 和位移 `v` 证明，若有限截断从 `T` 起满足 `HighwayFrom ... T Q v`，则 `C_n<=T`。理由是最后一个碰撞标记位于 `C_n-1`；假如某个周期尾部包含它，标记便会无限重复，最终进入已认证的标准尾部，而标准字不含该标记。

对于周期 104，结果进一步精确到一个时刻：

```text
H_n = 12915 + T_n = C_n + 311
```

`finiteSchedule_exact_highway_start` 证明从 `H_n` 起永久每 104 步平移 `(-2,-2)` 并恢复朝向，同时证明任何位移的永久 104 步公路都不能从小于 `H_n` 的时刻开始。这是精确最早起点，不只是充分上界。

证明不依赖扫描长轨迹来猜测永久性。定义 `recoveryColor` 为 548 步碰撞字接上无限标准字；`finiteSchedule_last_collision_reads` 对任意偏移证明它等于实际最后一段的读色。内核验证偏移 418 与 522 的颜色不同，并验证从 419 到 547 的全部 129 个偏移满足 104 步读色一致。通用 `HighwayFrom.extend_one` 证明：如果下一步已永久周期，且当前相隔一个周期的读色相同，则利用转向和移动的单射性可向前延伸一步。迭代 129 次把已认证的 548 起点精确提前到 419；偏移 418 的不一致排除所有更早起点。

这里需要区分几何公路与参考字的相位对齐。`HighwayFrom` 要求位置平移和朝向重复；`StandardHighwayFrom` 还指定读色参考字的起始相位。`finiteSchedule_earlier_standard` 证明相位对齐的证书从 `12940+T_n` 起成立，比几何公路起点晚 25 步，比旧充分起点提前 104 步。当前没有单独证明该相位对齐起点最早。

| 初始间距参数 | 最后障碍首次接触 | 精确最早 104 步公路 | 已证相位对齐起点 |
| --- | ---: | ---: | ---: |
| `[]`，一个障碍 | 12604 | 12915 | 12940 |
| `[0,1,2]`，四个障碍 | 14560 | 14871 | 14896 |
| `[0,3,1]`，四个障碍 | 14664 | 14975 | 15000 |

对递增序列 `f(i)=i`，精确几何起点为 `12915+52*n*(n+7)+132*n`。`finiteSchedule_onsets_unbounded` 对任意固定参数序列证明，其有限截断的永久公路起点无界，因此这不是充分上界增长造成的假象。以上结论仍只覆盖特定对角线障碍族，不推出任意有限支撑的主猜想。

## 强有界记忆与最终周期公路（L1）

`BoundedMemory.lean` 使用强定义：对每个 `n >= T`，当前格要么在最近 `W` 步内访问过，要么此前从未访问且在初态中为白。精确形式为

```lean
def BoundedMemoryFrom (s : State) (T W : Nat) : Prop :=
  forall n, T <= n ->
    (exists j, j < n ∧ n <= j + W ∧ (run s j).pos = (run s n).pos) ∨
    ((forall j, j < n -> (run s j).pos ≠ (run s n).pos) ∧ s.board (run s n).pos = false)

theorem BoundedMemoryFrom.highway {s : State} {T W : Nat}
    (h : BoundedMemoryFrom s T W) :
    exists U P v, T <= U ∧ 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s U P v ∧
      forall n, U <= n -> readColor s (n + P) = readColor s n
```

该定理不要求有限支撑。`EventuallyBoundedMemory.highway` 是存在量词版本，同样适用于任意初始棋盘。它给出某个正周期与非零整数漂移，不指定 104，也不规定标准读色字。

窗口 `memoryKey s n W` 保存当前朝向、前 `W` 次访问相对于当前位置的坐标及这些格子的当前颜色。每步各坐标变化不超过 1，因此在 `n >= W` 时，相对坐标均位于 `[-W,W]^2`。`memoryKey_mem` 将所有窗口放入显式有限列表 `memoryKeys W`；`finite_list_repeats` 给出重复窗口，`memoryKey_future` 证明后续窗口永久同步。相同读色及朝向使相应步的移动相同，`highwayFrom_of_memoryKey_eq` 因而得到固定漂移。

`HighwayFrom.drift_ne_zero` 对任意棋盘、任意正周期的公路排除零漂移：零漂移会使整个尾部的位置只落在一个周期的有限列表中，与 `escapes_finite_set_after` 矛盾。该论证没有把弱无界性升级成一般周期性；周期性来自额外的强有界记忆前提。若删除定义中的“初始为白”，前方未知黑格可能影响下一步，现有窗口决定未来的证明便不适用。

## 弹道性、有界记忆与主猜想分解（L3）

`Ballistic.lean` 令 `linearForm a b (x,y) = a*x+b*y`。`BallisticFrom s T a b p q C` 使用整数参数并显式要求 `p > 0`、`q > 0`、`C >= 0`；对所有 `T <= n <= m` 要求

```text
q * linearForm a b (pos(m))
  <= q * linearForm a b (pos(n)) - p * (m-n) + q*C
```

正整数 `p,q` 表示正有理速率，非负整数 `C` 表示统一回退界。`Ballistic s` 表示存在这些参数及起点。它比“任意晚仍能离开有限集合”强，也比没有速率与回退界的“最终永久离开有限集合”强。

```lean
theorem BallisticFrom.boundedMemory {s : State} {T : Nat} {a b p q C : Int}
    (h : BallisticFrom s T a b p q C) (hs : FiniteSupport s.board) :
    exists U, T <= U ∧ BoundedMemoryFrom s U ((q * C / p).toNat + 1)
```

整数除法给出 `floor(q*C/p)`，该商非负，所以窗口宽度就是 `floor(q*C/p)+1`。证明先由 `BallisticFrom.eventually_below` 得到线性坐标最终低于任意整数界，再由 `BallisticFrom.avoids_finite` 同时避开初始黑格与时刻 `T` 之前访问的有限集合。取最小值时加入整数锚点 0，因而空集情形也被覆盖，且显式保证 `U >= T`。此后若当前格曾被访问，弹道不等式给出两次访问的间隔上界；若未被访问，有限支撑保证它初始为白。

`Ballistic.boundedMemory` 与 `Ballistic.highway` 因而证明：有限支撑加弹道性推出最终强有界记忆、非零漂移的正周期公路及同周期读色。有限支撑只在 L3 中用于排除无限延伸的初始黑格，L1 本身无需此假设。

正向从标准公路的运动定义直接得到具体弹道参数，不依赖进入种子证书：

```lean
theorem HighwayFrom.ballisticFrom_of_diagonal {s : State} {T : Nat} {v : Point}
    (h : HighwayFrom s T 104 v) (hv : DiagonalDrift v) :
    exists a b, BallisticFrom s T a b 4 104 108
```

取两个系数为与漂移坐标相反的符号，每 104 步线性坐标下降 4，每一步的增加不超过 1。任意时间差拆成完整周期和不足 104 步的余段，即得回退界 108。该常数是充分界，不主张最优。

周期分类命题及最终分解为

```lean
def PeriodicIsStandard : Prop :=
  forall s : State, FiniteSupport s.board ->
    (exists T P v, 0 < P ∧ HighwayFrom s T P v) -> EventuallyStandard s

theorem highwayConjecture_iff_ballistic_and_periodicIsStandard :
    HighwayConjecture ↔
      (forall s : State, FiniteSupport s.board -> Ballistic s) ∧ PeriodicIsStandard
```

反向先经 L3、L1 获得某个正周期，再使用周期分类得到标准公路。两项合取条件都没有无条件证明，且没有声称它们在逻辑上相互独立。该等价定理不解决一般有限支撑猜想；它明确区分了速率及回退控制与标准周期分类这两个剩余证明义务。

## 主猜想与参考字

`Period104Conjecture : Prop` 表达任意有限初态最终满足 104 步位置平移和朝向重复，漂移向量为 `(±2, ±2)`。仅凭这个性质不在定义上指定标准转向字，因此另定义更精确的 `HighwayConjecture : Prop`。

`standardColor` 取全白初态、原点朝北运行 10000 步后的连续 104 次读色，按模 104 重复，作为明确的标准参考字。`StandardHighwayFrom` 同时要求公路漂移和所有未来读色与该参考字一致。存在量词中的起始时刻允许对齐循环相位，起始朝向允许四分之一转的旋转。

`blank_reference_check` 用内核计算验证全白初态第 10000 步开始的 104 次读色等于显式 `highwayWord`。`standardColor_eq_certifiedColor` 将原来的参考定义与已认证的读色字连接，主猜想的含义没有被更换。参考字现在已经证明最小读色周期为 104，但没有在本项目证明全白轨迹从第 10000 步起永久重复；已证明的永久尾部从第 12080 步起算。

`HighwayConjecture` 和 `Period104Conjecture` 仍没有无条件证明。`highwayConjecture_implies_period104` 仅证明强目标蕴含较弱目标，其前提明确包含未解决的强目标。

一般情形仍需新的论证保证任意有限初态最终进入某个标准公路证书的适用状态，或用其他方式推出同一结论。当前完成了稳定性、具体可达性与无界性，没有将无界性提升为一般的必然进入定理。

## 有限计算与无限棋盘的一致性

黑格列表实现经 `FiniteState.toState_run` 与原始模型连接；两个有限棋盘的颜色一致只需检查其黑格并集，并集外均为白色，此检查器的可靠性已有证明。

全白初态的长有限段使用 `PackedState` 位图。窗口为 `[-64,64) × [-64,64)`，每一步读取和翻色前检查当前位置；越界返回 `none`，不绕回、不夹紧、不模拟墙壁。`bitIndex_injective`、`packedRun_sound` 证明成功运行结果等于无限棋盘上的原始模型。

`checkPackedAgreement_sound` 遍历窗口内全部 16384 格，并检查目标种子的所有黑格位于窗口内，从而覆盖窗口内外的完整半平面匹配。窗口仅用于到达证书之前的有限段；无限尾部完全由不受窗口限制的归纳定理处理。

## 构建与检查

项目使用 Lean 4.36.0，仅依赖该版本自带的 `Std` 和证明生成型 `omega`，没有 Mathlib 或第三方 Lean 包。版本固定在根目录 `lean-toolchain` 中。

Windows 本地工具链位于 `tools/lean-4.36.0-windows/`，下载自 [Lean 官方发布](https://github.com/leanprover/lean4/releases/tag/v4.36.0)，原始 `tar.zst` 已核对发布资产 SHA-256：

```text
8b910f5395fe13b70f2f662831e3fdbd523686e4ec999919927b1c18b505b696
```

在仓库根目录的 PowerShell 中运行：

```powershell
& '.\tools\lean-4.36.0-windows\bin\lake.exe' build
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/EntranceChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/FirstContactChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/HighwayRecoveryChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/DelayedRecoveryChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/RecoveryCertificateChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/MultipleObstaclesChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/InfiniteHighwayChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/SpacedHighwayChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/VariableChainChecks.lean
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true scripts/ProofAudit.lean
```

若已通过 elan 安装固定版本，可直接运行 `lake build` 和 `lake env lean -DwarningAsError=true scripts/ProofAudit.lean`。可移除的工具链和 `.lake/` 构建产物已在 `.gitignore` 中排除。

`scripts/ProofAudit.lean` 输出主要定理的公理依赖。源文件未使用 `sorry`、`admit`、自定义 `axiom` 或 `native_decide`。经典逻辑和标准 Lean 公理的使用应以实际审计输出为准，不能把“没有占位证明”误读为“不依赖任何基础公理”。

`lakefile.toml` 将全部 41 个根目录证明模块列入默认构建，本次 `lake build` 的 84 项任务全部通过。新增模块和扩展后的 `VariableChainChecks.lean`、`ProofAudit.lean` 均以 `warningAsError` 通过。公理审计增加独立间距有限及无限链的首次访问、任意正周期起点下界、有限截断进入时间无界、公路向前延伸、精确恢复边界及更早相位对齐证书，输出仅包含标准依赖 `propext`、`Classical.choice`、`Quot.sound`。源文件扫描没有使用 `sorry`、`admit`、自定义 `axiom`、`unsafe` 或 `native_decide`；没有把一般有限支撑猜想加入证明依赖。

`scripts/EntranceChecks.lean` 用内核计算检查四种旋转及平移后的证书均被接受；种子后方新增 `(100,100)` 黑格仍被接受，前方新增 `(-100,-100)` 黑格则被拒绝。前方远处缺陷必须阻止当前永久延续证书成立，即使最初多个周期可能不受影响。脚本还检查零步搜索对已认证种子和全白初态的不同结果。

`scripts/FirstContactChecks.lean` 检查首次接触搜索的半开区间边界、首个命中、重复格子的集合语义、坐标相关界限、永久不接触的推导，以及三个具体恢复结果和恢复区域之外新增黑格的实例。额外条带中的缺陷会被该恢复匹配检查拒绝，不被误认为已认证安全。

`scripts/HighwayRecoveryChecks.lean` 检查含相邻外围历史的状态：它满足原始边界 0，但不满足旧的边界 7；等待相应周期后，新恢复定理仍适用。还以符号变量 `k` 检查所有周期编号的实例及全白轨迹的应用。`scripts/DelayedRecoveryChecks.lean` 将独立证明的首次访问时间与总首次接触判定器连接，检查显式坐标、符号参数恢复结论和碰撞前的起点排除。

`scripts/RecoveryCertificateChecks.lean` 检查重复坐标的编码、窗口越界拒绝、非法向外入口拒绝、四张新增证书的符号周期实例及第二条单黑格族的总首次接触判定。`scripts/MultipleObstaclesChecks.lean` 检查空链、三个障碍的明确坐标、第四个格子不在三障碍初态中，以及对符号参数 `n`、`i` 的恢复和首次访问定理。

`scripts/InfiniteHighwayChecks.lean` 检查无限链的方向、间距与非链上格子的颜色，实例化 548 步公路、无限支撑与非标准性，检查排除短周期的具体见证和符号量化结论，并调用有限观察窗口的精确耦合定理。

`scripts/SpacedHighwayChecks.lean` 检查初始位置和朝向、间距 10 的链上及非链上颜色、周期 652、756、1588 的实例、任意更晚的 104 步公路排除，以及一个没有任何不超过一百万的最终正周期的具体成员。新增检查覆盖所有参数的最小周期、具体半周期的排除、倍周期及正确位移的接受、错误位移的拒绝，以及跨周期的标记对齐和相邻相位的排除。它还通过 `spacedObstacles_zero` 将先前的最小周期定理应用到新族的零参数状态。

`scripts/VariableChainChecks.lean` 检查空参数列表与障碍数的约定、混合间距 `[0,3,1]` 的坐标与恢复时刻、非链上白格、符号有限参数恢复、递增链的明确坐标与访问时刻、所有最终正周期的排除、非单调无界间距的实例，以及有限截断的恢复和有限观察耦合。新增检查覆盖首次接触、精确几何起点、起点前一步对所有位移的排除、参考相位对齐，以及单障碍和两种不同四障碍列表的实例。

`scripts/RecoveryOnsetExplore.lean` 打印最后一个违反 104 步读色一致的偏移 418，只用于发现候选。精确边界和其后 129 个读色等式由 `ExactVariableRecovery.lean` 中的 `decide +kernel` 独立认证，探索输出不是证明依赖。

`scripts/FindCertificate.lean` 用哈希集合探索并打印候选种子，不是证明依赖。候选输出由根目录显式常量和内核检查重新验证。工具链与 `.lake/` 仍为忽略的可重建文件。

`scripts/ExploreCollisions.lean` 使用原生哈希集合计算候选入口、坐标范围和权重上界。它只用于提出证书；上述碰撞恢复定理和所需界限由根目录的 `decide +kernel` 及其可靠性定理重新验证，不信任探索程序输出作为证明。

`scripts/ExploreHighwayHistory.lean` 和 `scripts/ExploreHighwayPhases.lean` 分别探索保留历史长度与首次访问相位对恢复的影响。它们用于选择有限证书，均不是证明依赖。部分相位的探索轨迹越出原保护半平面，因此不能直接用相位 0、4 的局部证明覆盖所有相位；有限模拟中的恢复现象没有被作为一般稳定性的前提。

`scripts/ExploreMaturePhases.lean` 探索更长历史下的相位恢复，以及相位 4 恢复前缀的空间范围。探索只提供证书候选；相位 5 的完整 6645 步恢复和多障碍转移的 548 步范围、入口均由内核重新验证。

`scripts/ExploreInfinitePeriod.lean` 用于找出排除全部短周期所需的读色见证范围；该输出不参与证明。根目录中的 `obstacleWord_no_short_period` 独立以内核计算认证有限见证的存在。

`scripts/ExploreSpacedPeriod.lean` 搜索能区分碰撞段与标准段的短读色标记，找出六位字 `LLRLLL` 及偏移 107。该程序只用于发现候选，根目录的计算证书和一般窗口分类独立完成全部验证。

`scripts/ReferenceTrace.lean` 可运行全白初态参考字的有限计算，检查两段 104 步的读色、位移和朝向。该脚本只是定义约定的诊断，不导出无限重复定理，也不是逃逸证明的前提。

本次有限计算输出：第 10000 步位于 `(-16, 10)`、朝北；下一段 104 步的净位移为 `(-2, -2)`，朝向恢复，随后第二段 104 次读色与第一段相同。该结果核对了参考字的相位与坐标约定，没有证明任意后续段都会相同。

## 双前沿探索（2026-11-22）

新增 `RecordSupport`：对任意实际轨迹，若初始白格上的黑读在下一步进入 `s1*x+s2*y` 的新记录层（`s1,s2=±1`），该次黑读恰为该格的第二次访问。唯一的先前访问是同位置、同朝向的白读，支撑区间留在旧前沿之后；同前沿的支撑区间按时间严格分离。有限支撑确保充分靠前的格子初始为白。

新增 `RecordSupportExamples`：认证全白轨迹中不同前沿的区间 `[0,4]`、`[1,53]` 真正交错；同一前沿的相邻记录对 `(5,6)`、`(79,80)` 的支撑来源分别为 0 和 70，第二个来源不是上一对的第二记录时刻 6。这些反例否定一般有限轨迹上的两种局部捷径，不否定仅针对周期尾提出的更强命题。

新增 `PeriodicBackgroundWord` 与 `DualFrontCountermodel`：周期 44、完整位移 `(0,4)` 的无限背景轴向公路，具有两套增长的对角记录前沿及完整 `100001` gadget。四个前导黑读无先前物理访问，来自无限背景。已证明永久延续、非有限支撑和不存在任何更晚的 104 步公路。没有宣称 44 为最小周期，也没有得到有限支撑猜想的反例。

新增 `AxisClockObstruction`：排除在全部有限状态上逐步严格增长的横向二周期加性整数时钟，允许任意位置/朝向头部修正。证明用两个不同有限初态的四步轨迹增量相消；没有把它们误认为同一条周期轨道，也不排除非线性或周期尾专用的势函数。

五个模块已加入默认构建。本轮 `lake build` 通过 147 项任务；`D:/langtonsant/scripts/BrainstormChecks.lean` 的 33 项公理检查均只依赖标准三公理的子集。未使用 `sorry`、`admit`、自定义 `axiom`、`unsafe` 或 `native_decide`，未重建重型单黑格或原生枚举目标。详细推导、候选前提和复现命令见 `D:/langtonsant/research/brainstorm-results-2026-11-22.md`。

一般有限支撑最终周期化、非对角漂移排除、最小周期完整位移分类，以及周期无关的宽度/回访间隔上界仍未证明。
