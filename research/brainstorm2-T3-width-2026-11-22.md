# T3：两格对角漂移的宽度控制与分类缺口

日期：2026-11-22。任务定义：[brainstorm2-brief-2026-11-22.md](D:/langtonsant/research/brainstorm2-brief-2026-11-22.md)。本文件续写此前中断会话的骨架，所有本轮实验结果均已重新核验。

## 0. 当前结论与证据边界

**交付类型为（3）：准确定位失败的推理步骤。没有证明完整漂移 `(±2,±2)` 迫使标准字，也没有发现满足全部白背景自洽条件的非标准反例。**

本轮的实质结果是：给出一般混合尾迹的非齐次双通道恒等式，并以标准字的纯内核见证否定齐次推广；构造 `g=12`、完整位移预算 `(2,-2)`、宽度任意大的端口计数松弛族；最后用一个四步首次返回准确证明该族为何不是真实轨迹。计数松弛族有完整纸面验证，但不称为公路反例。

- 统一旋转至 `(2,-2)`，横向坐标必须取本原法向 `t=x+y`，宽度为被访问层的最大值减最小值。每层有两个完整平移类，以 `x mod 2` 区分；不能把两个类合并。
- 现有极值线刚性直接约束上、下两条极值层的访问次数与颜色，不提供反复剥层的闭包定理；`g<=2(W+1)` 的方向不能反转来取得宽度上界。
- `TwoCellDiagonalExtremal.lean` 中从双通道流量推出的多项模二递推明确依赖 `PureOddWake`，不能直接推广到标准字所在的一般混合尾迹情形。
- Jillhewar 的宽度排除给出下界，不给出统一上界。Ke 的固定尾迹或固定宽度周期上界已经存在，但其输入不是对全部未知周期尾迹的统一预算。

## 1. 量词、对象和现有有限化接口

任取 `P : Nat`、`P>0` 及 `w : Fin P -> Bool`，按模 P 延拓为 `Nat -> Bool`；R 为白读右转，L 为黑读左转。要求 `ConsistentWord P w`，初始朝北、周期末恢复朝向，完整漂移为 `(2,-2)`。令 `q_i=wordPos w i`、`0<=i<P`，并定义

```text
t(q)=q.x+q.y,  r(q)=q.x mod 2,
lo=min_i t(q_i), hi=max_i t(q_i), W=hi-lo,
m_(t,r)=#{i<P : t(q_i)=t and r(q_i)=r},
D_(t,r)=m_(t,r) mod 2,  g=sum_(t,r) D_(t,r).
```

两点同完整平移类当且仅当 `(t,r)` 相同；代表为 `(r,t-r)`，提升为 `ell_i=floor(q_i.x/2)`，稳定时间为 `tau_i=i-P*ell_i`。类内读色须按真实 tau 顺序为 `R,L,R,L,...`。不能用某个人为指定的端口顺序代替 tau 顺序。

严格宽度目标是

```text
exists W0 : Nat, forall P>0, forall w,
  ConsistentWord P w -> wordDrift P w=(2,-2) -> W(P,w)<=W0.    (U)
```

不要求 P 最小；存在量词在 P、w 的全称量词之前。四种对角符号由四分之一旋转运输，法向亦随之旋转。更强的标准字分类还需要完成有限候选的自洽判定，不能把 `W>=10` 当成 `W=10`，也不能把 `W=10` 当成标准字唯一性。

现有工具给出 `g<=2(W+1)`；Ke 的对角预算进一步给出
`P<=g*(3^(W/2)-1)<=2(W+1)*(3^(W/2)-1)`。因此一旦证明 (U)，数学上的有限化接口已经存在，尽管枚举可能不可行。反之，`g` 的上界与 `g<=2(W+1)` 不能推出 W 的上界；第 3 节甚至保持 g 恒为 12 而任意加宽。

极值层都是奇层，每个被访问的极值类恰有一次 R；因此访问支撑与奇类尾迹的最小、最大横向坐标相同，即二者跨度相等。这里“尾迹大小”必须区分类数 g 与横向跨度 W，控制前者不等于控制后者。见 [TwoCellDiagonalExtremal.lean:556](D:/langtonsant/TwoCellDiagonalExtremal.lean:556)、[PeriodicGrowthResidue.lean:555](D:/langtonsant/PeriodicGrowthResidue.lean:555)。

已阅读任务书、证明状态及相关背景的适用部分、上一轮漂移研究与完成的 T1 来源链接结果。本轮使用既有 `.olean`，没有重建依赖；其他线程的并发产物不属本轮所有权。

## 2. 已定位的非齐次项（纸面推导）

记 `e,w,n,s` 为指定类离开时朝 E、W、N、S 的事件数，其中小写 w 的计数下标与转向字 w 按上下文区分。对偶数层 `t`、通道 `r in {0,1}`，记 `D_(t,r)=m_(t,r) mod 2`，并在 `F_2` 中定义

```text
F_(t,r) = e_(t,r) + n_(t-1,1-r).
```

对所有满足本题假设的字，精确双通道流量恒等式给出

```text
F_(t+2,r) + F_(t,r) = D_(t,1-r) + D_(t+2,r).       (D)
```

证明：奇数层 `t+1`、通道 `1-r` 的守恒为
`s_(t+1,1-r)+n_(t+1,1-r)=w_(t+2,r)+e_(t,r)`；偶数层来向总数给出
`s_(t+1,1-r)+n_(t-1,1-r)=D_(t,1-r)`（模二），出向总数给出
`w_(t+2,r)+e_(t+2,r)=D_(t+2,r)`（模二）。相加并消去重复项即得 (D)。

因此 `PureOddWake` 将所有偶数层的 D 消为零之后，才得到
`pureOdd_step_invariant` 的齐次递推。对一般混合尾迹，把右边删去是无依据的。
有限支撑只使条带外 F 为零；向内传播时仍须累计右边的缺陷，不能推出内部 F 恒零，
更不能从模二零值推出自然数流量为零。

来源接口：[精确流量](D:/langtonsant/TwoCellDiagonalExtremal.lean:847)、[PureOddWake 等价式](D:/langtonsant/TwoCellDiagonalExtremal.lean:928)、[齐次递推](D:/langtonsant/TwoCellDiagonalExtremal.lean:991)。本轮已在仓库外临时文件中核验一般式，甚至只需朝向闭合及完整漂移，不需要白背景自洽假设；完整代码见第 7 节。

标准字 `stdHighwaySE` 给出 `t=-2,r=0` 时
`F_(-2,0)=0`、`F_(0,0)=1`、`D_(-2,1)=0`、`D_(0,0)=1`。
因此删去 (D) 右边的推广已被真正自洽标准字否定。

## 3. 任意加宽的计数松弛模型与明确时序障碍（已获纸面构造）

下述模型并非 `ConsistentWord`。它证明的是一组明确列出的必要条件不足以约束宽度，
并不证明所有可能的宽度机制不存在。

对每个整数 `n>=1`，从标准 `stdHighwaySE` 的逐类端口表出发：保留层 `0,...,8`，
把下极值层 `-1` 移至 `-1-2n`，上极值层 `9` 移至 `9+2n`；每通道插入 n 个下带和 n 个上带。
方向对表示“到达方向、离开方向”，每行按拟定的类内秩 `0,1,2,3` 排列：

| 插入层 | 每个通道的四个方向对 | 读取 |
| --- | --- | --- |
| 下带偶层 | `NE, SE, SW, SE` | `RLRL` |
| 下带奇层 | `ES, EN, ES, WS` | `RLRL` |
| 上带奇层 | `WN, EN, WN, WS` | `RLRL` |
| 上带偶层 | `NE, NW, SW, NW` | `RLRL` |

具体下带偶层为 `-2n,-2n+2,...,-2`，下带奇层为 `-2n+1,...,-1`；
上带奇层为 `9,11,...,7+2n`，上带偶层为 `10,12,...,8+2n`。
每个新类重数为 4，贡献两次 R、两次 L。按完整位移 `(2,-2)` 的类连接，
水平边翻转通道，竖直边保持通道。

该模型满足逐方向 incidence、逐类 R/L 计数、合法转向、固定到达轴、极值层单次 R，
总位移仍为 `(2,-2)`，且

```text
W_n=10+4n,   P_n=104+32n,   g_n=12.
```

**最强自我否定：** 即使按每类拟定秩对每条有向边作保序匹配，仍不能实现真实时间。
取最上插入奇层 `a=7+2n` 的任意通道 r。保序匹配强迫下面的四步路径：

```text
C_(a,r)[0] --N--> Q_(a+1,r)[0] --E--> C_(a+2,1-r)[0]
            --S--> Q_(a+1,1-r)[2] --W--> C_(a,r)[2].
```

此为一个单位方格的四边，物理位置恰回到起点，中间三个位置均不同。
因此真实稳定秩必须从 0 增到 1；指定端口表却从 0 增到 2，且两端都读 R。
这违反 `Drift.path_firstReturn_rank`，不只是缺少某个可选优化条件。
若强迫实现为几何转向字，该物理格的相邻两读均为 R，连一般初始颜色下的翻色交替也不成立。

Python 诊断中 `n=1,2,3,10` 的保序后继均为单个环、绕数为 1；仍不能由此推出自洽。
`n=1` 的顶侧类 `(9,0)` 实际稳定次序是拟定秩 `[0,2,1,3]`，读色 `RRLL`，
时间为 `[-489,-485,-329,-185]`（时间原点由脚本后继环起点固定）。
一般 n 的拒绝不依靠这些有限实验，而由上述四步首次返回证明。

### 3.1 松弛模型的精确量词

这里的模型 M 是有限的类到端口列表映射，不预设存在真实周期字。它满足以下条件 R：

1. 每个类具有一个有限列表；偶层到达轴竖直、离开轴水平，奇层相反；每个事件是合法的左转或右转。
2. 每类列表的读色从 R 开始交替，因此 `#R-#L=m mod 2`。这仍只是**指定列表顺序**上的交替。
3. 每条完整商有向边的出端口数等于到端口数；水平边翻转通道、竖直边保留通道。
4. 访问层为连续有限区间；上下极值均为奇层、各通道一个事件，顶层 `E->S`、底层 `W->N`，均读 R。
5. 总方向增量为 `(2,-2)`，`P≡0 mod 4`、`g≡0 mod 4`、`g>=8`；两个棋盘奇偶均有奇类；每个 x 或 y 模二余数类的奇类棋盘符号和为 `2 mod 4`。

**纸面命题：** 对每个 `n : Nat`，上述显式 M_n 满足 R，且 `W(M_n)=10+4n`、`g(M_n)=12`、`P(M_n)=104+32n`。所以

```text
forall B : Nat, exists M, R(M) and g(M)=12 and W(M)>B.       (R-unbounded)
```

该量词结论只否定从 R 推出统一宽度上界的论证。它既不否定 (U)，也不声称 R 包含全部已知必要条件。

### 3.2 逐项证明及预算

`M_0` 取已认证标准字的真实稳定端口列表，故满足 R。对每个通道，新增下带偶层的到向计数为 `(N,S)=(1,3)`、出向为 `(E,W)=(3,1)`；新增下带奇层到向为 `(E,W)=(3,1)`、出向为 `(N,S)=(1,3)`。上带分别为：奇层到向 `(E,W)=(1,3)`、出向 `(N,S)=(3,1)`；偶层到向 `(N,S)=(3,1)`、出向 `(E,W)=(1,3)`。

由此每个带内接口逐方向匹配；两通道使用相同表，所以水平边通道翻转也匹配。标准层 0 每通道恰有一个 W 出端口和一个 N 到端口；标准层 8 每通道恰有一个 E 出端口和一个 S 到端口。新下、上带保留这四个边界接口，最外端分别接到移动后的 `W->N` 与 `E->S` 单例。故所有接口守恒。标准边界计数本轮另用 `standard_interfaces` 经 `decide +kernel` 核验，来向数由精确有向边守恒转换；不是猜测的额外假设。

一个下带两层、两通道贡献 16 个事件、净位移 `(4,-4)`；一个上带贡献 16 个事件、净位移 `(-4,4)`。成对加入的净位移为零、事件增量为 32。每个新类重数 4，对 g 的贡献为零；原有奇类仅将四个极值类移动偶数层，棋盘符号与 x/y 模二余数都保持。因此 g、混合奇偶、模四余数全部继承标准字。上下极值各移动 2n，得到所述宽度公式。有限支持外全部计数为零，支撑内每层被访问，类邻接图保持连通。

这些计数还满足第 2 节的带缺陷恒等式，因为它只依赖精确 incidence；所以修正非齐次项本身仍没有消除宽化族。

### 3.3 不可实现性不是“尚未找到拼接”

若 M_n 的指定列表真的是真实稳定顺序，固定有向边的匹配必按该顺序逐项配对，见 [DriftRank.lean:783](D:/langtonsant/DriftRank.lean:783) 及 [TwoCellAxial.lean:1724](D:/langtonsant/TwoCellAxial.lean:1724) 中的有序列表实例。

在顶带 C_(a,r)，第一个 N 出端口来自秩 0，第二个来自秩 1，第三个来自秩 2；顶带 Q_(a+1,r) 的第一个 N 到端口正是秩 0。其 E 出端口唯一，接到顶极值单例。极值 S 出端口也唯一，接到另一通道 Q 的唯一 S 到端口（秩 2）。这一步后的 W 出端口为该 Q 的第二个 W，因而返回 C 的第二个 W 到端口（秩 2）。于是四步路径完全被强迫。

四步总空间位移为 `N+E+S+W=0`，总提升量为零；这一回返不受跨周期接缝或周期幂的影响。在 `C[0]` 和 `C[2]` 间不可能再出现 C 的物理位置，故必须是相邻真实稳定秩，与指定的秩 1 位于其间矛盾。见 [DriftRank.path_firstReturn_rank](D:/langtonsant/DriftRank.lean:560)。

更具体的时间约束是 `tau_succ-tau=1-P*liftStep` 与每类 `tau_0<tau_1<...` 必须同时成立。只在人工列表上保序，没有证明这些不等式能与同一组 tau 兼容。诊断例甚至具有单个后继环和正确总绕数，说明“商图连通、单环、净位移正确”仍不足以补上这一缺口。这里单环诊断仅对列出的 n 做过检查，没有把它推广为所有 n 的定理；任意 n 的不可实现性已经有独立四步证明。

## 4. 向内剥层为什么不能直接迭代

极值刚性依赖完整轨迹不越过该极值。删去最外层访问后，原先经过该层的两个步长一的转移会被接成一段宏步；它通常不是蚂蚁的一次合法步长一转移。新边界颜色包含被删访问造成的历史改变，也不自动具有白首读。尚无将“剥去极值层”送回 `ConsistentWord` 的变换。

标准字给出直接检验：极值为 `-1,9`，分别只有单次 R；紧邻的 `0,8` 层类重数均为 `(3,4)`，会读黑，不能套上原极值的单例结论。若删去两层而想保留奇层类型，剩余原层 `1,7` 的重数分别为 `(3,6)` 与 `(6,3)`，仍不满足新极值应有的单例结构。因此朴素剥层并不在目标模型内封闭。

这一例子只否定未经修正的剥层；它没有排除使用附加边界状态、宏步或历史变量的其他归约。若提出此类变换，需要重新证明步法、边界首读、真实稳定次序及完整漂移如何变化。

## 5. Jillhewar / Ke 的来源范围与本轮区别

固定 Jillhewar 版本为 `76a7e234e577d992d086c204c3dea00ae72cf10a`。本轮直接下载并阅读 [paper/main.tex](https://github.com/Atharva12456/langtons-ant-highway/blob/76a7e234e577d992d086c204c3dea00ae72cf10a/paper/main.tex)。`thm:extremal` 给出极值刚性；`thm:width6`、`thm:width8` 分别排除 W=6、8，结合此前结果得偶数 `W>=10`。宽度 6 的块松弛为 6 列、357 个边界状态；宽度 8 为另一个 8 列块。其计算完备性未在 Lean 形式化，本轮没有执行外部检查器，也没有重新认证计数。

这些全周期宽度排除的量词覆盖任意对角完整漂移 `(m,-m)`，并非只在 P 的某个截断内搜索。但它们给出的是下界；原文 `rem:width4` 亦明确保留宽度 10 的轨迹分类问题。不能由“标准字达到已知最小宽度”推出任意轨迹都达到最小宽度。

固定 Ke 版本为 `b3429c25c33519c14f58f0a7171a857092bbd4cc`。本轮直接阅读 [wake_synthesis/PROOF.md 第 8 节](https://github.com/kehao95/langtons-ant-core/blob/b3429c25c33519c14f58f0a7171a857092bbd4cc/wake_synthesis/PROOF.md#L414)。其两侧时钟与交叉流量递推已经控制**给定**尾迹的周期，且导出 `P<=g*(3^(W/2)-1)`。这不是未知轨迹的统一 W 上界。

本轮并未改进这些排除范围或预算。增加的是：显式缺陷恒等式、标准字否定齐次推广的内核证据、固定 g=12 的任意宽计数族，以及该族在四步物理首次返回处的精确时序矛盾。不主张该类松弛构造在全部文献中的新颖性。

## 6. propose -> refute -> verify 的对抗检查

1. **标准字与拟定齐次递推。** 已认证 `stdHighwaySE` 的 `P=104,v=(2,-2),W=10,g=12`。本轮 `decide +kernel` 核验 `m_(0,0)=3,e_(0,0)=2,n_(-1,1)=1`，以及所需外侧零值；由此证明它不满足 `PureOddWake`，且 F 确有非零缺陷。这是真正自洽周期字的反证，不依赖伪模型。
2. **任意幂与旋转。** 解析上，标准字的 n 次幂采用 `(P,v)=(104n,nv_std)` 时物理轨迹不变，完整类细分，`W=10,g=12n`。所以不能在重复字上仍用每层两类，或把 g=12 写成不限制完整漂移的全称定理。四分之一旋转必须同时旋转法向；任意移相必须重新计算提升。上述几何与首次返回论证均不依赖选取的相位或周期代表。
3. **实际有限回归。** 独立 Python 从第 7 节显式字计算 `n=1,2,3,4`、全部 104 个移相、四种旋转，共 1664 实例；检查全部稳定首白交替、`g=12n`、本原法向宽度 10、每条后继边的时间补偿，累计 341120 次相邻真实首次返回，全部通过，最大间隔 116。该有限回归不代替任意 n 的解析说明。负漂移提升使用欧几里得余数，未误用负除数的 Python 向下整除。
4. **跨周期提升。** [RecordSupportExamples.standard_sources](D:/langtonsant/RecordSupportExamples.lean:125) 中相位 21 的白源相位为 33，实际时间为 `33-104=-71`，不是 33 晚于 21 的相位比较。回归使用 `tau=i-P*ell`；宽化模型的四边总提升严格为零，故不存在用跨周期平移逃避该回返矛盾的余地。
5. **最强宽化自我反驳。** 第 3 节证明对所有 `n>=1`，人工稳定表在同一物理格上强迫 `R` 后四步再读 `R`；从真实轨迹上看它是直接的翻色错误。有限诊断的 `n=1,2,3,10` 均通过 incidence、局部转向、R/L 数、增长余数、单环和总绕数检查，仍在真实稳定顺序上失败。因此未将计数解误报为自洽反例。
6. **局部振荡子。** 重新复现 Jillhewar 的单列例子：黑格行为 `{1,2}`，从第 2 行朝 E 进入，读 `LR` 后黑格变 `{1,3}` 并朝 E 离开；外部重新指定第 2 行朝 W 进入，读 `RL` 恢复 `{1,2}` 并朝 W 离开。它提供合法局部循环，否定单列必须耗尽的朴素势函数，但未给出外部返回的真实连线，因此不是公路。本轮的宽化失败也不声称所有局部循环都不合法。
7. **RecordSupportExamples 与 T1。** 已读并通过现有 `.olean` 确认 `crossing_distinct_fronts`、`source_link_fails`、`standard_sources` 的签名。跨前沿支撑 `[0,4]` 与 `[1,53]` 真正交错，暂态相邻记录对的下一来源为 70 而非 6；故未使用通用层叠或来源自动覆盖。T1 的标准公路边界偏移 `0,-1,-2,2,1,0` 还否定边界接触空间单调性，不能把它隐含到剥层。上述暂态反例未被当作周期宽度反例。

## 7. 最小 Lean 引理、可复现输入与信任边界

一般非齐次恒等式适合作为下一步先纳入工具层的最小引理。以下代码在临时文件中实际通过，未写入仓库 Lean 模块：

```lean
import TwoCellDiagonalExtremal

namespace LangtonsAnt.T3Research
open TwoCellDiagonal

theorem mixed_step_defect {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    (eCnt P w (t+2) r + nCnt P w (t+1) (!r) +
      eCnt P w t r + nCnt P w (t-1) (!r)) % 2 =
    (classMult P w t (!r) + classMult P w (t+2) r) % 2 := by
  have hf := odd_layer_flow_eq hh hd (show (t+1) % 2 = 1 by omega) (!r)
  have ha := even_layer_arr_sum hh hd ht (!r)
  have he := even_layer_dep_sum (P := P) (w := w) (show (t+2) % 2 = 0 by omega) r
  rw [Bool.not_not] at hf
  have ht2 : t+1+1 = t+2 := by omega
  have ht0 : t+1-1 = t := by omega
  rw [ht2, ht0] at hf
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem standard_defect :
    classMult 104 stdHighwaySE 0 false = 3 ∧
    eCnt 104 stdHighwaySE 0 false = 2 ∧
    nCnt 104 stdHighwaySE (-1) true = 1 ∧
    classMult 104 stdHighwaySE (-2) true = 0 ∧
    eCnt 104 stdHighwaySE (-2) false = 0 ∧
    nCnt 104 stdHighwaySE (-3) true = 0 := by
  decide +kernel

example : ¬ PureOddWake 104 stdHighwaySE := by
  intro hp
  have hm := (pureOddWake_iff_even_classMult_even stdHighwaySE_drift).mp hp
    0 false (by decide)
  rw [standard_defect.1] at hm
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem standard_interfaces :
    ∀ r : Bool,
      wCnt 104 stdHighwaySE 0 r = 1 ∧
      nCnt 104 stdHighwaySE (-1) r = 1 ∧
      eCnt 104 stdHighwaySE 8 r = 1 ∧
      sCnt 104 stdHighwaySE 9 r = 1 := by
  decide +kernel

#print axioms mixed_step_defect
#print axioms standard_defect
#print axioms standard_interfaces
end LangtonsAnt.T3Research
```

核验命令：

```powershell
$env:LEAN_PATH='D:/langtonsant/.lake/build/lib/lean'
& 'D:/langtonsant/tools/lean-4.36.0-windows/bin/lean.exe' -M1536 -DwarningAsError=true 'G:/TEMP/brainstorm2-t3-width-20261122/Checks.lean'
```

退出码 0，三条具名定理的公理依赖均恰为 `[propext, Classical.choice, Quot.sound]`；未用 `native_decide`、`sorry` 或新增公理。对第 3 节的整个宽化族及其首次返回矛盾，本轮提供纸面证明，**未端到端形式化**。

独立诊断输入为 [StandardHighway.lean:38](D:/langtonsant/StandardHighway.lean:38) 中的字：

```text
LLRLRRRRLRLLLLRRRRLRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRLLRRLLLLRRLLRRRRLLRRLRLLRLLRLRLLRRRRLLRLLRRRRLLRRRR
```

复现流程：朝北、原点起步，R 右转、L 左转后移动；字左移 7 位得到 `stdHighwaySE`。按 `(x+y,x mod 2)` 分类，以 `i-104*floor(x/2)` 排序，得到 M_0 的类列表。按第 3 节保留中部、移动极值及插入四种列表，得到 M_n。对每条类有向边，把源出列表与目标到列表按拟定秩逐项配对；枚举后继环时，每条边提升为 `floor((r+dx)/2)`。一个环若长 P、总提升 1，从任意起点令累计提升为 ell，则每事件真实时间候选为 `i-P*ell`；重新逐类排序并检查首白交替。`n=1` 即给出 `RRLL` 失败，不需要搜索更长周期。

读取外部来源时 web 工具端点返回 404，本轮改用只读 HTTPS 下载固定 SHA 原始文本到临时目录；未执行外部脚本。Python 仅执行本轮创建的诊断程序；检查对象不含其他用户目录或服务。

## 8. 剩余问题与执行记录

真实字的 (U)、固定完整漂移 `(±2,±2)` 的标准字分类、以及任意有限初态最终周期化仍未解决。尤其没有证明一般真实周期尾迹可以任意宽，也没有证明任意 g=12 的自洽字就是标准字。

可以准确排除的路线是：从本轮明确列出的 R 计数条件取得宽度上界；删除混合尾迹的缺陷项；把极值线刚性未经闭包证明地反复向内应用；以及把人工类内保序匹配直接认作真实时间实现。若继续研究，应保留跨周期提升、每类真实稳定次序与首次返回相邻秩，并寻求一个能排除**所有**宽化方式的全局约束。排除本轮一种局部带不能推成全局宽度分类。

仓库内仅续写本指定结果文件，未修改其他文件、未提交、未启动子代理、未执行 `lake build`。

**清理记录：** 本轮创建的 `Checks.lean`、`explore.py`、`experiment.log`、两个下载的来源文本及 Python 缓存已在校验绝对路径后删除。该实验目录原先已有此前会话留下的 `width_checks.py`，本轮未运行、未修改，也未删除该既有文件；剩余目录与文件的完整路径为 `G:/TEMP/brainstorm2-t3-width-20261122/width_checks.py`。因此目录本身仍保留，按任务允许的替代方式报告精确路径。本轮所用 Lean 代码、标准字输入、宽化列表和复现算法已保存在第 3、7 节，不依赖剩余脚本。
