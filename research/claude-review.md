# 独立审阅：单格翻色归约、进入证书与推进一般有限初态的候选引理

审阅日期：2026-11-20
审阅范围：`SingleFlipReduction.lean`、`HighwayEntrance.lean`、`drafts/proof-status.md`，以及它们直接依赖的定义（`LangtonsAnt.lean`、`Highway.lean`、`FirstContact.lean`、`EntranceChecker.lean`、`MaskedAgreement.lean`）。
本次未修改任何现有 Lean 文件。第 2.3 节的两个新等价定理在临时文件中对现有工程编译通过（见附录 A），尚未加入仓库。

标记约定：

- **[Lean 已验证]**：在本工程上编译通过，公理仅 `propext`、`Classical.choice`、`Quot.sound`。
- **[完整证明]**：本文给出完整数学证明，未形式化。
- **[证明梗概]**：论证思路清楚，但细节未逐一核对，可能需要补条件。
- **[开放]**：据我所知没有证明，也没有反例。

---

## 1. 结论摘要

1. `highwayConjecture_iff_currentCellFlipStability` 的证明正确，量词没有遗漏。`CurrentCellFlipStability` 与原猜想逻辑强度相同：正向证明只是把 `HighwayConjecture` 直接用在 `flipCell s s.pos` 上，在这个方向的证明中没有用到前提 `EventuallyStandard s`。这个归约的价值在于指明“一次翻色”是唯一需要控制的操作。等价本身不说明证明难度是否降低；换成更适合归纳或局部分析的形式，仍可能让证明变容易。
2. 归约可以收窄到更具体的形式，两者都等价于原猜想 **[Lean 已验证]**：
   - `AddBlackStability`：只需要“白变黑”的翻色，翻色位置任意，不必在蚂蚁脚下。
   - `FreshObstacleStability`：只需要在首次访问时刻、对初始为白的格子做脚下翻色。也就是说，原猜想等价于“给任意最终标准的有限初态添加一个初始障碍，结果仍最终标准”。“已有公路遇障恢复”的完全一般形式因此就是原猜想本身，其难点全部在**进入公路之前的混乱阶段发生的碰撞**。
3. 只对**已进入公路之后**的翻色成立的稳定性，哪怕覆盖全部 104 个相位和任意历史，也不能经由现有归纳推出原猜想。原因是加入一个障碍会产生新的过渡期，下一个障碍可能正好在这个过渡期内被碰到（第 3.2 节）。
4. 我建议的核心新引理是一个不依赖 104 的结构性结论 **[完整证明]**：

   > 有限支撑轨迹若最终具有**有界记忆**（每次读取的格子要么从未被访问过，要么在最近 `W` 步内被访问过），则最终是周期平移公路（周期 `P > 0`，位移 `v ≠ 0`）。

   作为推论，“沿某个线性方向以正速率前进、回退量有界”（弹道性）就足以得到最终周期性。由此原猜想恰好分解成两个独立的开放问题 **[完整证明]**：

   ```text
   HighwayConjecture ⇔ (∀ 有限 s, Ballistic s) ∧ PeriodicIsStandard
   ```

   **[Lean 已验证，2026-11-20 由 Codex 形式化，Claude 独立复核公理]** L1 为 `BoundedMemoryFrom.highway`（`BoundedMemory.lean`）；L3 与分解定理为 `highwayConjecture_iff_ballistic_and_periodicIsStandard`（`Ballistic.lean`）。`BallisticFrom` 显式要求 `p > 0`、`q > 0`、`C ≥ 0`。两个合取项仍是开放命题。

   前者是纯动力学的“以速率逃逸”，后者是“有限支撑下的周期运动只能是标准公路”的分类问题。这是两个性质不同的待证义务，本文没有证明它们在逻辑上相互独立。仅有“最终离开每个有限集合”是不够的，所缺的正是**速率**和**回退界**这两个量化条件（第 3.1 节）。
5. 在“公路遇障恢复”方向上，我认为切实可做的下一步有两个：
   - 证明“按权重充分分离的任意二维前方障碍集”都会恢复。这需要先算出有限多个首访相位 `Φ_fresh` 的恢复证书。
   - 完成任意单黑格定理。它可以化为有限多个首访相位证书，加上一个有限早期格集合的逐个计算（第 3.3 节）。

   两者都不能直接推出一般结论。
6. 没有找到有限支撑猜想的反例。仓库里的无限链反例在本文中只用来证明“某种推理方式不成立”，不被当成反例。

---

## 2. `CurrentCellFlipStability` 等价归约的审查

### 2.1 证明逐步核对

`highwayConjecture_iff_currentCellFlipStability` 由三段组成，我逐一核对如下。

**(a) HC ⇒ CCFS。** `finiteSupport_flipCell` 保证 `flipCell s s.pos` 有有限支撑，直接应用 HC 即可。前提 `EventuallyStandard s` 未使用，所以 CCFS 中的这个前提在逻辑上是多余的，它只在反方向的归纳中起作用。

**(b) CCFS ⇒ ArbitraryCellFlipStability。** 设 `mask = (· = p)`，`firstContact_or_never` 给出两种情形。

- 若参考轨迹在时刻 `T` 首次读到 `p`，则由 `firstContact_state` 得到 `run (perturb mask s) T = perturb mask (run s T)`。等式右侧保留了参考运行的全部历史棋盘。此时 `(run s T).pos = p`，`run s T` 仍有有限支撑（`finiteSupport_run`），并且仍最终标准（`EventuallyStandard.run`）。对它应用 CCFS，再用 `EventuallyStandard.of_run` 拉回到原状态。
- 若永不接触，则由 `perturb_standard_of_avoids` 直接得到结论。

`EventuallyStandard.run` 的证明先把起点后移 `104*n` 步（`shift_periods`），保证新起点不早于 `n`，处理正确。

**(c) ACFS ⇒ HC。** 对黑格列表归纳，起点 `whiteAt p d` 是任意位置和朝向的全白状态（`whiteAt_standard`）。重复元素按集合语义处理。`finiteSupport_representable` 保证每个有限支撑状态都有精确的列表表示。归纳假设对 `p`、`d` 全称量化，量词顺序正确。

结论：证明正确，没有隐藏的有界性假设，也没有把有限模拟当作前提。

### 2.2 归约强度的说明

- 由于 `flipCell` 是对合，`flipCell s s.pos` 可以是任意有限状态。CCFS 真正的约束在于前提“`s` 最终标准”，而这个前提本身就是原猜想的一个实例。所以 CCFS 是原猜想的**同等强度重述**。它在逻辑上不更弱，但这不排除它的形式更便于归纳。
- 正向证明不使用 `EventuallyStandard s`，只说明该方向的证明用不到它，不能据此说可以从稳定性命题中随意删去这个前提。
- CCFS 的量词覆盖处于过渡期任意时刻的状态，翻色时的历史棋盘也完全任意。现有六个相位的恢复定理只覆盖“已在公路上”的状态，文档第 167、219 行已经正确指出了这一点。

### 2.3 收窄后的两个等价形式 [Lean 已验证]

从 2.1(c) 的归纳可以看出，每次加入的格子 `q ∉ cells` 在当前状态中都是白色的。从 2.1(b) 可以看出，在首次接触时刻，这个格子此前从未被访问过，所以颜色仍是初始的白色。由此得到：

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

含义如下：

- 不需要处理“黑变白”的翻色，也不需要处理“重复访问格”的翻色。
- 需要的只是：**一个从开始就存在、首次被碰到的白格障碍**不会破坏最终标准性。

这正是“已有公路遇障恢复”的形式，只不过量词覆盖碰撞发生在过渡期的情形。后续各节都以 `FreshObstacleStability` 为基准讨论缺口。

---

## 3. 三个方向分别还缺什么

### 3.1 “最终离开每个有限集合”

#### 3.1.1 三个逐级增强的命题

```text
Unbounded s     :≡ ∀ K 有限, ∀ T, ∃ n ≥ T, pos(n) ∉ K
EscapeForever s :≡ ∀ K 有限, ∃ T, ∀ n ≥ T, pos(n) ∉ K
                   （等价于：每个格子只被访问有限次）
Ballistic s     :≡ ∃ 整数 a b，∃ 自然数 p q (p > 0, q > 0)，∃ 自然数 C，∃ T,
                   记 ℓ(x,y) = a*x + b*y，对所有 T ≤ n ≤ m：
                   q*ℓ(pos m) ≤ q*ℓ(pos n) - p*(m-n) + q*C
                   （沿方向 ℓ 以速率 p/q 前进，回退量不超过 C）
```

`Unbounded` 已经证明（`escapes_finite_set_after`），并且对任意棋盘都成立。`EscapeForever` 和 `Ballistic` 对有限支撑状态都是 **[开放]**；两者都可以由 HC 推出，见 3.1.4。

#### 3.1.2 有界记忆引理 [完整证明]

**定义。** 称 `s` 从时刻 `T` 起具有 `W`-有界记忆，当且仅当对所有 `n ≥ T`，记 `c = pos(n)`，下列两条至少有一条成立：

- (i) 存在 `j` 满足 `n - W ≤ j < n`，使得 `pos(j) = c`；
- (ii) 对所有 `j < n`，`pos(j) ≠ c`，并且 `s.board c = false`。

**引理 L1。** 若 `s` 从某时刻起具有 `W`-有界记忆，则存在 `T'`、`P > 0` 和 `v ≠ (0,0)`，使得 `HighwayFrom s T' P v` 成立，且读色也以 `P` 为周期。

**证明。** 对 `n ≥ max(T, W)`，定义窗口状态

```text
σ_n = ( dir(n),
        (pos(n-i) - pos(n))  for i = 1..W,
        board_n(pos(n-i))    for i = 1..W )
```

它取值于一个大小不超过 `4 · (2W+1)^(2W) · 2^W` 的有限集合。下面说明下一步完全由 `σ_n` 决定：

- 若 `pos(n)` 出现在窗口里，读到的颜色就记录在 `σ_n` 中；
- 否则由条件 (ii)，读到的是白色。

于是转向、移动方向和新窗口（加入当前格并翻色，丢弃最旧的一项）都是 `σ_n` 的函数，记 `σ_{n+1} = F(σ_n)`。由抽屉原理，存在 `n1 < n2` 使 `σ_{n1} = σ_{n2}`，从而对 `n ≥ n1` 有 `σ_{n+P} = σ_n`，其中 `P = n2 - n1`。每步的位移由 `σ_n` 决定，所以 `pos(n+P) - pos(n)` 等于一个周期内位移之和，是常数 `v`。朝向和读色同样以 `P` 为周期。若 `v = 0`，则 `n1` 之后的轨迹落在有限集合中，与 `escapes_finite_set_after` 矛盾。∎

注意（第 1、2 条已按 Codex 的审阅意见修正）：

- 上述 L1 的强定义已在条件 (ii) 中要求“初始为白”，所以 **L1 本身不需要有限支撑**，对任意初始棋盘都成立；排除零漂移用的 `escapes_finite_set_after` 也适用于任意棋盘。
- 弱定义只要求“最近 `W` 步内重访，或者首次访问”，不要求初始为白。在弱定义下需要有限支撑：实际发生的首次访问初始黑格的时刻有限，把起点移到它们之后，就得到强定义。无限支撑的例子失效，是因为它们不满足强定义（前方首访格可以是黑色），而不是 L1 的论证有缺陷。
- L1 只给出某个周期 `P`，**不**给出 104。

#### 3.1.3 弹道性推出有界记忆 [完整证明]

**引理 L3。** 若 `s` 有有限支撑且满足 `Ballistic s`，则存在 `T''`，使 `s` 从 `T''` 起具有 `W`-有界记忆，其中 `W = ⌊C·q/p⌋ + 1`。因此由 L1，`s` 最终是周期公路。

**证明。** 设 `K0` 为初始黑格集合，`V_T` 为时刻 `T` 之前访问过的格子集合，两者都有限。由弹道性，`ℓ(pos m) → -∞`。取 `T'' ≥ T`，使得对所有 `m ≥ T''`，`ℓ(pos m) < min ℓ(K0 ∪ V_T)`；若 `K0 ∪ V_T` 为空，这个条件自动成立，只需 `T'' = T`。形式化时可以加入一个锚点，避免对空集取最小值。对 `m ≥ T''`，记读取的格子为 `c = pos(m)`，它不属于 `K0 ∪ V_T`，分两种情形：

- 若 `c` 在 `m` 之前被访问过，则最后一次访问时刻 `n` 满足 `n ≥ T`。由 `ℓ(pos n) = ℓ(pos m)` 和弹道不等式得 `p(m-n) ≤ qC`，即 `m - n ≤ W`，条件 (i) 成立。
- 否则 `c` 从未被访问且不在 `K0` 中，因此是白色，条件 (ii) 成立。∎

#### 3.1.4 原猜想的分解 [完整证明]

定义

```text
PeriodicIsStandard :≡ ∀ s, FiniteSupport s.board →
  (∃ T P v, P > 0 ∧ HighwayFrom s T P v) → EventuallyStandard s
```

则

```text
HighwayConjecture ⇔ (∀ s 有限支撑, Ballistic s) ∧ PeriodicIsStandard
```

- **⇒** 直接从 `HighwayFrom` 推出弹道性，不需要种子证书（Codex 给出的简化）。对漂移 `v = (±2,±2)`，取 `ℓ(x,y) = -sgn(v.x)·x - sgn(v.y)·y`：每个周期 `ℓ` 下降 4，每步变化不超过 1。把时间差写成 `104k + r`，就得到统一常数，例如 `p = 4`、`q = 104`、`C = 108`。`PeriodicIsStandard` 的结论本身就是 HC 的结论。
- **⇐** 由 L3 和 L1 得到最终周期性，再由 `PeriodicIsStandard` 得到标准公路。

两个合取项各自都是 **[开放]**。这个分解把问题分成两个性质很不相同的部分：

- **动力学部分（Ballistic）：** 是否必然以正速率、有界回退地逃逸。`EscapeForever` 比它弱：既没有速率，也没有回退界，所以推不出有界记忆。“最终离开每个有限集合”所缺的就是这两个量化条件。
- **分类部分（PeriodicIsStandard）：** 由 L1 的证明可知，有限支撑下的周期尾部必定对应某个有限自动机 `F_W` 的一个“诚实”圈，也就是从它自身的窗口棋盘（其余全白）出发能永远跟随该圈的圈。因此对每个固定的 `W`，命题 `PeriodicIsStandard_W` 可以化为有限检查：枚举 `F_W` 的所有圈，对每个圈检查有限多个时滞上的自交（时滞上界由 `v ≠ 0` 的线性增长给出）**[证明梗概]**。但 `W` 没有上界，所以有限计算不能覆盖整个命题。我不知道 RL 蚂蚁是否存在非 104 的“白色前方”公路，文献核查中也没有确认这一点。

#### 3.1.5 无限支撑例子说明了什么（不是反例）

由 `proof-status.md` 记录的已证界限，可以推出 `growingObstacles`（间距递增的无限链）满足 `EscapeForever`，而且**满足 `Ballistic`**，但它没有任何最终正周期。推导梗概如下：

- 每段公路都处在其入口框架的 `x+y ≤ 0` 半平面内（548 步碰撞前缀和标准段都已证明这个界）；
- 入口框架原点的权重每段至少下降 16，每段耗时不超过 `548 + 104 f(i)` 步，权重下降 `16 + 4 f(i)`；
- 所以速率下界取 `min(16/548, 4/104)`，回退界取常数。

这条推导我没有在 Lean 中形式化 **[证明梗概]**。Codex 指出：只有整段的平均速度和单侧半平面界，还不足以推出对所有 `n ≤ m` 成立的弹道不等式，还需要控制块内部相对线性趋势的波动。可以把每段拆成固定长度的 548 步碰撞块和若干 104 步标准子块，再单独处理区间两端的残段。我认为结论可以补上，但在补完之前，这仍只是梗概。

若补全，它说明：**弹道性加任意棋盘推不出周期性**。L3 中“前方未访问格为白”的有限支撑条件不可去掉。这与有限支撑猜想不冲突。

### 3.2 “有限次局部扰动”

#### 3.2.1 不加限制的“有限扰动稳定性”就是原猜想

设 `seed0 = highwaySeed.toState`（原点朝北，已在公路入口）。对任意有限状态 `u`，先用 `normalize u.dir u.pos` 把它归一化为原点朝北，得到 `u'`，再令 `M = u'.board xor seed0.board`。`M` 是有限集合，且 `u' = perturb M seed0`。因此

```text
HighwayConjecture ⇔ ∀ M 有限, EventuallyStandard (perturb M seed0)
```

**[完整证明，需配合现有的 `EventuallyStandard.pose` 与 normalize 引理]**

“任意有限扰动下的公路稳定性”与原猜想等价，没有更容易。要从“扰动稳定性”得到真正的进展，必须**同时**做到两件事：

- 限制扰动的种类（例如位置、间距、发生时刻）；
- 给出一个机制，把一般状态化归到这类受限扰动。

后者目前完全缺失。

#### 3.2.2 为什么“公路之后的单次翻色稳定性”不能闭合归纳

设想把现有六个相位的结论推广到全部相位和任意历史，得到如下命题 **[开放]**：

```text
LateFlipStability :≡ ∀ s 有限支撑, ∀ T r origin, EntryAt s T r origin →
  ∀ n ≥ T, EventuallyStandard (flipCell (run s n) (run s n).pos)
```

在 2.1(c) 的归纳中，第一个格子 `q1` 若在参考状态进入公路之后才被首次碰到，就可以使用 LateFlip，得到最终标准的新状态 `s1`。但 `s1` 有自己的过渡期 `[0, T1)`。第二个格子 `q2` 可能在 `s1` 的过渡期内被首次碰到，这时 LateFlip 不适用。

`run s 0` 本身也可能处于过渡期。最直接的例子是在全白初态的脚下加一个黑格：首次接触发生在 `τ = 0`，而全白状态在时刻 0 不满足 `EntryAt`，因为模板在归一化原点处是黑格。注意 12080 只是**已认证**的入口时刻，不是已证明的最早入口，所以不能把 `[0,12080)` 整段都称为过渡期。

我没有构造“LateFlip 成立但 HC 不成立”的模型，所以只能说：**现有归纳方式**推不出原猜想，不能说 LateFlip 在逻辑上必然不够。

能闭合的是下面这个**条件定理** **[完整证明，依赖 LateFlip]**：

```text
LateOrderable u :≡ 存在 u 的初始黑格的一种排列 q1,...,qn，使得记
  u_0 = 全白（同位置朝向），u_i = u_{i-1} 加上 q_i，
  对每个 i，参考 u_{i-1} 对 q_i 的首次接触（若存在）
  不早于 u_{i-1} 的某个入口时刻。

LateFlipStability → ∀ u, LateOrderable u → EventuallyStandard u
```

`MultipleObstacles` 和 `VariableFiniteObstacles` 都是 `LateOrderable` 的具体实例。缺口在于：一般 `u` 不满足 `LateOrderable`，例如初始黑格密集在蚂蚁附近的情形。

#### 3.2.3 单调量

“尚未被读取的初始黑格数”随时间单调不增，并最终稳定。稳定之后剩余的那些格子永不被访问，可以删除而不改变轨迹（`perturb_standard_of_avoids`）。

这一点在一般情形下没有用处：它不能限制过渡期的长度，也不能阻止蚂蚁反复读写自己的遗迹。`ObstacleChain` 的归纳之所以有效，是因为每段转移都有显式的时间和空间界，而不是因为这个量单调。

### 3.3 “已有公路遇到障碍后恢复”

#### 3.3.1 首访相位

标准公路的时刻 `104k + φ`（从入口算起，`k` 足够大）所在的格子是 `c_φ + k·(-2,-2)`。当 `k` 足够大时，这个格子此前是否被访问过只取决于 `φ`：过渡期遗迹的权重有下界，而 `c_φ + k·v` 的权重趋于 `-∞`，其余部分由平移周期性决定。记

```text
Φ_fresh = { φ < 104 | 对充分大的 k，c_φ + k·v 在时刻 104k+φ 首次被访问 }
```

前方的白格障碍只能在 `φ ∈ Φ_fresh` 的相位上被首次碰到（因为 `FreshObstacleStability` 只涉及首次访问）。所以前方障碍的恢复只需要 `|Φ_fresh|` 张证书，而不是 104 张。

**[Lean 已验证，`FreshPhases.lean`]** 对种子轨迹已证明完整分类，阈值 `K0 = 2`：

```lean
theorem seed_firstVisit_iff {k phi : Nat} (hk : 2 <= k) (hphi : phi < 104) :
    FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ freshPhases
```

这里的首次访问相对于从时刻 0 开始的整个历史。`freshPhases` 共 22 个相位：

```text
[4, 5, 6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 66, 94, 95, 96]
```

已认证的 4、5、66、94、95 都在其中；尚缺恢复证书的有 17 个。`seed_late_cell_white` 另外证明：`k ≥ 2` 时这些目标格在种子初态中都是白色。

证明的关键在于：一个周期内的权重范围是 `[-9,0]`，所以只需比较同周期更早的相位和前两个周期。对所有 `k` 的结论由平移推出，不是有限扫描的结果。移植到全白初态时，还需另行排除入口之前的历史访问。

#### 3.3.2 按权重分离的任意二维前方障碍 [证明梗概，依赖有限证书]

**所需证书。** 对每个 `φ ∈ Φ_fresh`，需要一张 `RecoveryCertificate (104·H_φ + φ) D_φ origin_φ`，并满足：

- (C1) 恢复后的朝向与原公路相同，即仍朝西南；
- (C2) 恢复期间的读取范围满足 `weight ≥ w(q) - a_φ`，其中 `q` 为碰撞格；这一条需要在现有证书之外额外检查；
- (C3) 历史需求 `H_φ` 有限（相位 5 目前用了 12 个周期）。

**候选定理。** 令 `G = max_φ (a_φ + 4·H_φ + 4) + 常数`。对所有满足 `AgreesBelow 0 s highwaySeed.toState` 的 `s`，以及所有满足下列条件的有限格子列表 `cells`：

- 每个元素的权重都不超过 `-c0`；
- 任意两个不同元素的权重差至少为 `G`；

都有 `EventuallyStandard (perturb (mask cells) s)`。

**证明梗概。** 对剩余障碍数归纳。

- 当前框架下，若公路永不碰到剩余障碍，则由 `perturb_standard_of_avoids` 得到结论。
- 否则取首次被碰到的 `q`，其相位 `φ ∈ Φ_fresh`。用 `RecoveryCertificate.after_entry` 得到新入口。由 (C2) 和分离条件，其余障碍在恢复期间不会被读取，并且在新框架下仍位于前方。由 (C1)，新框架与旧框架方向一致。

这里用到的是 `AgreesBelow.run_perturb`，它可以携带剩余掩码，现有文件中已有。

**意义与边界。**

- 它把 `MultipleObstacles` 从固定对角线推广到任意二维位置，只要求权重分离。
- 若某个 `φ` 的恢复转向别的方向，(C1) 失效，就要改用二维分离，并重新分析前方的定义。
- 它不涉及过渡期，所以仍不能推出一般结论。

**可能的有限支撑反例形状。** 若某个首访相位的碰撞**不恢复**，那么“种子加有限公路遗迹加前方一个黑格”就是一个有限支撑状态，可能构成真反例。但要确认不恢复，必须给出无限时间证明（例如另一个周期的公路证书），模拟中长时间不恢复不算数。

#### 3.3.2a 首访相位恢复的实际计算结果（2026-11-20 补充）

候选由 `scripts/ExploreFreshPhaseRecovery.lean` 的有限模拟给出，只用来提出候选；“已验证”一律指 `decide +kernel` 检查通过。

1. **同向恢复：** 相位 37、47、52 的 `RecoveryCertificate` 已通过内核检查，对应 `H` 分别为 10、3、5。原有的 4、5、66、94、95 也属于这一类。
2. **转向恢复：** 在历史足够长的稳定区间，多数首访相位恢复到**转了四分之一圈**的公路。新公路朝西北（入口朝东）或朝东南（入口朝西），漂移权重为 0，所以它与原前沿线平行，永远不会回到历史区域。
   - 为此新增了 `RotatedRecovery.lean`。其中 `RotatedRecoveryCertificate` 的可靠性定理已编译通过；对整个无限尾部的权重界，用的是已认证的一周期位置表加零权重漂移。
   - 相位 9、15、22、23、24、32、33、34、39、48、96 的转向证书已通过内核检查。
3. **相位 6、38：** 证书已通过内核检查。相位 6 是转向恢复，`H = 18`；相位 38 是同向恢复，`H = 13`，因为路径超出位图窗口，用 `checkShiftedRecovery` 先平移 `(20,20)` 再检查，平移后的可靠性也已证明。

**[Lean 已验证]** 综合定理（`HardPhaseRecovery.lean`）：

```lean
theorem fresh_phase_recovers_except_49 (phi : Nat) (hphi : phi ∈ freshPhases) (h49 : phi ≠ 49) :
    exists H : Nat, forall s : State, AgreesBelow 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos)
```

也就是说，22 个首访相位中有 21 个，在入口保护半平面之外的历史任意、之后再过任意多个周期的情况下，脚下翻色都最终标准。唯一的例外是相位 49。
4. **相位 49（已按 Codex B 的探索更正，仍是有限观察）。** 对 `H = 11, 12, 25, 50, 100`：
   - `checkEntry` 首次成功的位置都在绝对坐标 `(39,-37)`，朝南（新公路朝东北），延迟为 `52213 + 104·(H-11)`。
   - 我原先把这个现象解释为“蚂蚁沿旧遗迹走回原始区域”，**这个解释是错的**。

   Codex B 的比较结果如下：
   - `H = 11` 与 `H = 100` 的轨迹，在平移 `(-178,-178)` 后，前 52300 步的位置、朝向、读色完全相同。
   - 两者棋盘之差始终是同一组 1068 格，全部位于旧公路窄带 `-2 ≤ x-y ≤ 8` 内。
   - 第 51046 步起出现周期 104、漂移 `(2,2)` 的运动，位置在 `x-y ≈ 75`，远离旧公路窄带。

   所以更合理的解释是：蚂蚁在旧公路旁边的平行位置生成了一条朝东北的公路，它朝种子原区所在的权重方向前进，却不经过旧窄带。入口坐标之所以固定，是因为半平面证书要求新公路**整个前方半平面**都与模板一致，而这个半平面包含旧历史；只有越过这些历史之后，`checkEntry` 才会成功。

   推论：
   - 这条恢复路径会进入 `x+y > 0`，所以不存在“历史任意、只要求 `AgreesBelow 0`”的证书。
   - 但它可能只依赖一条有界宽度的条带（`x-y ≈ 75` 附近）为白色。需要的新证书形态是**条带型**的保护区域，而不是半平面。
   - 到达后的完整棋盘与 `H` 有关（`H = 12` 与 `H = 100` 相对 `H = 11` 分别有 2438 和 6140 个差异格），所以不能声称它与历史无关。

   **[Lean 已验证，2026-11-21，`TrailRetrace.lean`]** 条带型证书已经完成：

   - 历史长度为 13 个周期时，52421 步前缀只读取 `x+y ≤ 0` 或条带外的格子，这一步由内核检查。
   - 东北公路的尾部 `x-y ∈ [68,78]`，对全部时刻都在条带外，这是证明，不是模拟。
   - 由此得到 `phase_forty_nine_recovers`：对每个满足 `TrailAgreement 0 s seed` 的 `s`（棋盘只在条带内、权重为正处与种子不同）和每个 `k`，翻色后都从第 52421 步起进入漂移为 `(2,2)` 的标准公路。

   合并后的 `all_fresh_phases_recover` 覆盖全部 22 个首访相位。边界有两点：相位 49 的前提比其余 21 个更强；全白初态的过渡期遗迹不在条带内，所以这个结论不能直接用到全白初态上。

对 3.3.2 的影响：

- (C1) 对多数相位不成立。“仅按权重分离的多障碍”定理需要改用二维分离，并在每次转向后重新确定“前方”。
- (C2) 对相位 49 不成立：新公路朝东北，会进入任意远的 `x+y > 0` 区域。

要处理相位 49，所需的新引理形态是**条带型公路证书**：只要求新公路经过的那条有界宽度的条带与模板一致（或者是白色），而不是整个前方半平面。同时还要单独核对条带与旧历史的交集。对种子和全白初态，这些交集是有限的具体格子，例如 Codex B 指出的 `(2,-1)`；对任意历史则无法保证。这一部分由 Codex B 在 `TrailRetrace.lean` 中进行，尚未证明。

#### 3.3.3 任意单黑格定理的有限化方案 [证明梗概]

目标：`∀ p d q, EventuallyStandard (whiteAt p d 在 q 处加一个黑格)`。由对称性，可以设蚂蚁在原点朝北。

1. 参考轨迹取全白初态。若它永不访问 `q`，由 `decideBlankContact` 的总判定，加上 `perturb_standard_of_avoids` 即可得到结论。
2. 若首次访问时刻 `τ ≥ 12080 + 104·H`，其中 `H = max_φ H_φ`，则相位 `φ = (τ - 12080) mod 104` 属于 `Φ_fresh`。用该相位的证书，配合 `RecoveryCertificate.after_entry`，即可得到结论；`DelayedRecovery.lean` 和 `MaturePhaseRecovery.lean` 已对相位 4、5 完成了这一步。
   补充：第 3.3.2a 节表明，相位 49 没有与历史无关的证书，这一步对相位 49 不成立。对全白初态，相位 49 的碰撞会让蚂蚁回到全白轨迹的过渡区域。需要先证明逆行证书，再对全白历史另做一次有限计算；若到达时的状态与 `k` 无关，这一次计算就够了，但这一点尚未证明。
3. 若 `τ < 12080 + 104·H`，`q` 落在一个**有限**集合 `E` 中，即全白轨迹在该时刻之前访问过的格子，元素数不超过这个时刻数。对每个 `q ∈ E`，用 `searchEntry` 分别给出内核验证的入口证书。

这是一个**有限**但可能很大的计算。若 `E` 中某个格子在给定预算内找不到入口，结论只能记为“未定”，不能记为反例。

`research/highway-conjecture-status.md` 记载的 Hao Ke 预印本声称已证明这一定理，本次未独立核验。

#### 3.3.4 固定黑格数 n 的推广 [证明梗概，未核对完整性]

沿 3.3.3 的思路对 n 递归：

- 每一层的参考状态都已知最终标准；
- 下一个被碰到的格子，要么在当前参考状态的有限早期集合中，要么在“晚期”首访相位上；
- 晚期碰撞的结果是以碰撞周期编号为参数的族，平移不变性使其余的相对位置情形有限。

我认为对**每个固定的** `n`，`HC_n`（恰好 n 个初始黑格）都可以化为有限多个有限检查，再加上 `Φ_fresh` 证书。但是：

- 情形数随 `n` 至少指数增长；
- 递归中“小参数 `k`”分支的有限性，需要逐层核对恢复路径是否回到更早的遗迹区域；
- 若真的证明了 `∀ n, HC_n`，就得到一般猜想，并不需要统一的时间上界（原稿中“不对 n 一致所以推不出”的理由有误，已按 Codex 意见修正）。目前缺的是：一个对任意 `n` 都成立的有限化论证，以及所有分支确实都能拿到成功证书。“每个固定 `n` 看起来可以计算”只能让人逐个处理有限多个 `n`，不能得出 `∀ n`。

---

## 4. 关于反例的边界

- 仓库中所有非标准例子（`infiniteObstacles`、`spacedObstacles k`、`scheduledObstacles f`）都具有无限支撑，并且**前方永远不是白色**，所以它们与 `PeriodicIsStandard` 的有限支撑版本无关，也不是 HC 的反例。
- 这些例子严格说明了三件事：
  - (i) 有限截断在每个有限窗口内与无限链一致，不能传递“最终标准”（文档已写明）；
  - (ii) 弹道性加无限支撑推不出周期性（3.1.5，证明梗概）；
  - (iii) 障碍逐个恢复的组合定理所给的恢复时间必然随障碍数增长，不存在对所有 n 一致的起点。
- 本次没有构造有限支撑状态的不恢复例子，也没有进行任何把模拟当证明的推断。

---

## 5. 对现有文档的小意见

1. `proof-status.md` 第 167 行写到“该等价关系不能被‘23 黑格种子翻转后会恢复’替代”。这句话是对的，但可以补充：CCFS 正向不使用 `EventuallyStandard s`，归约本身不降低强度（第 2.2 节）。
2. 建议在“脚下翻色的等价归约”一节加入 2.3 的两个收窄形式。它们说明一般问题只涉及“首次碰到初始白格障碍”，从而把 `FreshCollision` 和 `MaturePhaseRecovery` 的工作与一般猜想更直接地对接起来，同时也清楚地划出了它们未覆盖的部分，即过渡期碰撞。
3. 第 47–49 行关于逃逸定理的边界描述准确。建议把 `EscapeForever` 和 `Ballistic` 作为命名的开放命题写出来，以免读者把 `escapes_finite_set_after` 误读为“最终离开每个有限集合”。
4. 第 478 行已注明 `scheduledObstacles_visits` 没有证明首次访问，这点很好。3.1.5 的推导不依赖首次访问。

---

## 6. 建议的优先级

分工已与 Codex 商定，见 `research/claude-codex-sync.md`。

1. **已由 Codex 完成：** 附录 A 的两个等价定理已并入 `FreshObstacleReduction.lean`，尚未接入默认构建。
2. **Codex 进行中：** 在 `BoundedMemory.lean` 中形式化 L1；计划在 `Ballistic.lean` 中形式化 L3 和分解定理。
3. **Claude 负责：** 在 `FreshPhases.lean` 中计算 `Φ_fresh` 并证明完整分类定理（第 3.3.1 节），然后为每个首访相位寻找满足 (C1)–(C3) 的证书。这一步是 3.3.2 和 3.3.3 的共同前提。
4. **大型有限计算：** 按 3.3.3 完成任意单黑格定理，并评估 `E` 的规模以及 `decide +kernel` 的成本。
5. **开放问题（不预期短期解决）：** `Ballistic` 对一般有限初态是否成立，以及 `PeriodicIsStandard` 是否成立。

---

## 附录 A：已编译的等价定理

以下代码保存在临时文件中，以 `import SingleFlipReduction` 编译。编译命令为：

```powershell
& '.\tools\lean-4.36.0-windows\bin\lake.exe' env lean -DwarningAsError=true <file>
```

编译通过，输出为：

```text
'LangtonsAnt.highwayConjecture_iff_addBlackStability' depends on axioms: [propext, Classical.choice, Quot.sound]
'LangtonsAnt.highwayConjecture_iff_freshObstacleStability' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```lean
import SingleFlipReduction

namespace LangtonsAnt

def AddBlackStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall q, s.board q = false -> EventuallyStandard (flipCell s q)

def FreshObstacleStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall T, s.board (run s T).pos = false ->
      (forall j, j < T -> (run s j).pos ≠ (run s T).pos) ->
      EventuallyStandard (flipCell (run s T) (run s T).pos)

theorem addBlackStability_implies_highway (h : AddBlackStability) : HighwayConjecture := by
  have hlist : forall cells p d, EventuallyStandard (stateOfCells cells p d) := by
    intro cells
    induction cells with
    | nil =>
      intro p d
      exact ⟨12080, rotatePoint d (-2, -2), diagonal_rotated_southwest d, whiteAt_standard p d⟩
    | cons q cells ih =>
      intro p d
      by_cases hq : q ∈ cells
      · have heq : stateOfCells (q :: cells) p d = stateOfCells cells p d := by
          have hb : (fun x => decide (x ∈ q :: cells)) = fun x => decide (x ∈ cells) := by
            funext x
            by_cases hx : x = q <;> simp [hx, hq]
          simp only [stateOfCells, FiniteState.toState, hb]
        rw [heq]
        exact ih p d
      · have heq : stateOfCells (q :: cells) p d = flipCell (stateOfCells cells p d) q := by
          have hb : (fun x => decide (x ∈ q :: cells)) = flip (fun x => decide (x ∈ cells)) q := by
            funext x
            by_cases hx : x = q <;> simp [flip, hx, hq]
          simp only [stateOfCells, FiniteState.toState, flipCell, hb]
        rw [heq]
        apply h _ (FiniteState.finiteSupport ⟨cells, p, d⟩) (ih p d) q
        simp [FiniteState.toState, hq]
  intro s hs
  obtain ⟨f, hf⟩ := finiteSupport_representable s hs
  have hh := hlist f.black f.pos f.dir
  change EventuallyStandard f.toState at hh
  rw [hf] at hh
  exact hh

theorem highwayConjecture_iff_addBlackStability : HighwayConjecture ↔ AddBlackStability := by
  constructor
  · intro h s hs _ q _
    exact h _ (finiteSupport_flipCell hs q)
  · exact addBlackStability_implies_highway

theorem freshObstacle_implies_addBlack (h : FreshObstacleStability) : AddBlackStability := by
  intro s hs hst q hq
  rw [flipCell_eq_perturb]
  rcases firstContact_or_never (fun x => decide (x = q)) s with ⟨T, hT⟩ | hnever
  · apply EventuallyStandard.of_run (n := T)
    rw [firstContact_state hT]
    have hp : (run s T).pos = q := by simpa using hT.1
    have hfresh : forall j, j < T -> (run s j).pos ≠ (run s T).pos := by
      intro j hj
      rw [hp]
      simpa using hT.2 j hj
    have hh := h s hs hst T (by rw [hp]; exact hq) hfresh
    rw [hp, flipCell_eq_perturb] at hh
    exact hh
  · obtain ⟨T, v, hv, hstd⟩ := hst
    exact ⟨T, v, hv, perturb_standard_of_avoids hstd hnever⟩

theorem highwayConjecture_iff_freshObstacleStability :
    HighwayConjecture ↔ FreshObstacleStability := by
  constructor
  · intro h s hs _ T _ _
    exact h _ (finiteSupport_flipCell (finiteSupport_run s hs T) _)
  · intro h
    exact addBlackStability_implies_highway (freshObstacle_implies_addBlack h)

end LangtonsAnt
```

---

## 附：2026-11-21 进展，任意单黑格定理已证明

**[Lean 已验证]** `SingleBlackTheorem.lean` 中的 `singleBlackAt_standard p d q`：在全白棋盘上只放一个黑格 `q`，蚂蚁的位置 `p` 和朝向 `d` 任意，蚂蚁最终运行标准 104 步公路。公理只有标准的三个。

证明结构见 `drafts/proof-status.md` 中“任意单黑格初态”一节：

- 晚期碰撞：利用第 3.3.2a 节的 22 个首访相位结果。其中相位 49 需要单独处理全白遗迹，见 `Phase49Blank`。
- 早期碰撞：对 2215 个具体格子逐个给出内核证书。

这对应第 3.3.3 节提出的“任意单黑格定理的有限化方案”，现已全部落实。与该节预想的差别在于：相位 49 不能直接复用与历史无关的证书，需要额外证明全白遗迹与新公路的交互；这一点在当时未能预见。

对一般猜想的意义仍然有限。这一结论只覆盖单个初始黑格；第 3.3.4 节所说的对 n 个黑格做有限化，情形数增长极快，而且早期格子的穷举没有可以直接推广到多黑格的结构。
