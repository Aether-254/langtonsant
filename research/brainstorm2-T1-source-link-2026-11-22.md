# T1：来源链接与零净滑移——边界首次重复的精确缺口

日期：2026-11-22。任务定义：[brainstorm2-brief-2026-11-22.md](D:/langtonsant/research/brainstorm2-brief-2026-11-22.md)。

## 0. 结果类型与结论

**交付类型为（3）：准确定位失败的推理步骤。候选 B 和周期零净滑移均未证明，也未找到满足全部白背景自洽条件的反例。**

相对于[上一轮结果](D:/langtonsant/research/dual-front-results-2026-11-22.md)，本轮进一步把缺口化为一个明确的边界首次重复选择问题，并给出两种不能跨越它的推理及核验见证：

1. 在相邻记录对之间，旧最高层的接触字必为
   `z_0,z_1,...,z_r,z_rho`，其中 `z_0,...,z_r` 两两不同、均为首次白读，最后一次为 `z_rho` 的第二次访问。已知定理保证 `0 <= rho <= r`；**B 要求额外证明 `rho=0`**。
2. 同前沿来源支撑严格分离，给出的时间预算是
   `P = 2N + sum ell_k + sum delta_k`，其中 `delta_k >= 0` 是上一记录对的第二记录与下一来源之间的空档。B 等价于所有空档为零，亦等价于 `sum ell_k=P-2N`。**分离只给出 `sum ell_k<=P-2N`，不能把它改成覆盖等式。**
3. 真实标准公路在同一旧前沿上的接触偏移为 `0,-1,-2,2,1,0`。它否定“边界白接触按空间顺序单调”“所有额外接触均应排除”等桥梁，而且该见证本身满足全部周期自洽条件。全白暂态的相邻两个间隔又给出滑移 `-2,+1`，否定不使用周期性的统一单侧滑移引理。
4. 对一个固定增长前沿，零净滑移等价于 `s1*a=s2*b`；对所有白背景自洽字与所有增长前沿量化，零净滑移命题恰好等价于完整漂移对角性 `a^2=b^2`。不能把周期性本身当作这一结论的证明。

第 2—5 节为完整纸面推导；第 6 节明确区分纯内核核验、诊断计算和未证明命题。本文没有声称形式公理系统中的不可推导性，也没有把失败桥梁的反例当作 B 的反例。

## 1. 量词、时间与信任边界

任取 `P : Nat`、`P>0`，以及 `w : Fin P -> Bool`，将其按模 P 延拓。要求朝向在 P 步后恢复、完整漂移 `v=(a,b)!=0`，并满足仓库 `ConsistentWord P w`。白读为 R，黑读为 L。**不要求 P 最小，也不约分 v。**

设周期内位置为 `q_i`，双向几何轨迹定义为

```text
x_(kP+i) = q_i + k v,        k in Z, 0<=i<P.
```

每个固定物理格的访问是有限个相位各至多一次，按真实整数时刻排序后读色从 R 开始交替。这里使用的是完整平移类与稳定秩，不把相位编号大小当作物理时间顺序：

```text
tau_i = i-P*lift(v,q_i),
访问 base(v,q_i)+M v 的时间 = M P + tau_j.
```

接口见 [PeriodicWordCore.lean:71](D:/langtonsant/PeriodicWordCore.lean:71)、[DriftRank.lean:242](D:/langtonsant/DriftRank.lean:242)、[DriftRank.lean:560](D:/langtonsant/DriftRank.lean:560)。

再任取 `s1,s2 in {1,-1}`，使 `F(v)>0`，其中

```text
F(x,y)=s1*x+s2*y,
u=(s1,s2),  t=(s1,-s2),
D=F(v)=2N,  N>0.
```

整数时间上的记录指严格超过所有更早时间的 F 值。沿用上一轮已推导的记录对索引：前导黑读为 `m_k`，`k in Z`，且

```text
m_(k+N)=m_k+P,
A_k=x_(m_k),
C_k=x_(m_k+2)=A_k+u,
F(A_(k+1))=F(A_k)+2,
A_(k+N)=A_k+v.
```

`j_k<m_k` 是 `A_k` 唯一先前访问，读取 R，且与 `m_k` 同朝向；稳定秩分别为 0、1。来源唯一性使用 [RecordSupport.lean:178](D:/langtonsant/RecordSupport.lean:178)，同前沿时序使用 [RecordSupport.lean:206](D:/langtonsant/RecordSupport.lean:206)。

**有限初态版本的限定。** `ConsistentWord` 与有限初态周期实现之间的桥梁已在 [PeriodicWordRealization.lean](D:/langtonsant/PeriodicWordRealization.lean) 建立。对于真实 `FiniteSupport s.board`、`HighwayFrom s T P v`，本文的记录描述对应充分晚的记录：须越过初始黑集、暂态足迹与周期入口边界。不能断言任意 `m>=T` 的 `RunRecord` 都已具有双向轨迹的记录结构。任何双向见证都可平移到任意晚的周期副本，因此这一“充分晚”限定不会消除周期 B 的反例。

## 2. propose：边界接触字的首次重复正规形

### 2.1 精确陈述

在第 1 节的全部假设下，对每个 `k in Z`，置

```text
h=F(C_k),   c=m_k+2,   b=m_(k+1).
```

把有限区间 `[c,b]` 内满足 `F(x_n)=h` 的全部时刻严格递增列出：

```text
t_0=c < t_1 < ... < t_r < t_(r+1)=b.
```

则存在唯一 `rho in {0,...,r}`，使：

1. `z_i=x_(t_i)`，`0<=i<=r`，两两不同；每次都是该格在双向轨迹中的首次访问，读 R，稳定秩 0。
2. `x_b=z_rho`，`j_(k+1)=t_rho`；末次读 L，稳定秩 1，且 `[t_rho,b]` 是合法的物理首次返回。
3. 全部边界接触具有相同到达方向；其右转离开使 F 减少，左转离开使 F 增加。
4. 因而
   `C_k=A_(k+1) <-> rho=0 <-> j_(k+1)=m_k+2`。

这不是新的公路分类结论，而是对缺失连接的精确化。

### 2.2 完整证明

**未突破前的区域。** C 是上一对的第二记录，故 `n<c` 时 `F(x_n)<h`。下一对的第一记录在 `b+1`，因此 `n<=b` 时 `F(x_n)<=h`。于是全部边界格在 c 之前都未被访问；到达高度 h 必来自 h-1，不能来自 h+1。

**固定到达方向。** 同一 F 层上的格子具有相同棋盘奇偶，因为 `F(x,y)=x+y mod 2`。朝向轴与棋盘奇偶绑定，故所有这些接触的到达轴相同；在固定轴上，使 F 增加的方向只有一个，所以到达方向相同。C 是记录对中的第二格，其白读右转后回到 h-1；因此同层全部接触右转均减小 F，左转均增大 F。

**突破前全部读白。** 若某个 `t_i<b` 的接触读黑，则下一步已经到达 h+1，违反 `b+1` 为下一记录。故全部前末接触读 R。

**前末接触不重复。** 该层在 c 之前未被访问，首读为白。若前末接触中出现重复，取该格的第二次接触；两次之间没有同格访问，故第二次必读黑，与前段全部白读矛盾。于是 `z_0,...,z_r` 两两不同且均为首访。

**末次选择。** b 为下一记录对的前导黑读，初始白首读条件要求存在先前白源；该源位于同一格、同一高度，所以只能是上述某个 `t_rho`。前末接触的互异性保证 rho 唯一。它之前没有同格访问，且它与 b 之间无同格访问，故稳定秩严格为 0、1，完全满足 `path_firstReturn_rank`，没有用颜色相反代替秩相邻。

最后，由互异性，末端位置等于 `z_0=C_k` 当且仅当 rho=0，亦即来源时间等于 c。证毕。

### 2.3 仍未证明的唯一选择步骤

现有黑读来源、同前沿支撑分离和类内首次返回结论证明了

```text
exists unique rho in {0,...,r}, x_b=z_rho.
```

它们没有把存在量词中的 rho 指定为 0。每个不同的 `z_i` 都有自己的秩零，末次只对被选中的 `z_rho` 升到秩一，其他候选不需要同步返回。

因此，若继续证明 B，应证明一个真正使用**全局白背景周期性**的命题：

> 每个增长前沿的每个上述边界接触字，首次重复必重复其第一项。

它与 B 等价，不是已经获得的更弱定理。第 6 节说明为什么不能替换成空间单调、只有一个边界接触，或不使用周期性的局部选择规则。

## 3. 来源支撑的时间预算：分离不等于覆盖

对每个 k 定义

```text
ell_k=m_k-j_k > 0,
delta_k=j_(k+1)-(m_k+2) >= 0.
```

上述正规形给出 delta 非负，且 delta、ell 均以 N 为周期。逐项有

```text
m_(k+1)-m_k = 2 + delta_k + ell_(k+1).
```

对任意 `k0 in Z` 的 N 个连续下标求和，并用 `m_(k0+N)-m_k0=P`，得到精确等式

```text
P = 2N + sum_(k=k0)^(k0+N-1) ell_k
       + sum_(k=k0)^(k0+N-1) delta_k.                 (T)
```

令上一轮的沿前沿滑移为

```text
A_(k+1)=C_k+eta_k*t.
```

正规形保证

```text
eta_k=0 <-> delta_k=0 <-> rho_k=0,
2*abs(eta_k) <= delta_k.                             (L)
```

第二式来自两个同高格的曼哈顿距离；第一式还用了两端均为首次访问，因此不能有“经过一段非空闭合游走后再次成为首次访问”。

由非负性与周期性，固定字、固定前沿的 B 等价于

```text
forall k, delta_k=0
<-> sum_(k=k0)^(k0+N-1) delta_k=0
<-> sum_(k=k0)^(k0+N-1) ell_k=P-2N.                  (B-time)
```

**精确失败点：** 同前沿支撑互不相交，只能推出 `(T)` 中的 `sum ell_k<=P-2N`。若声称它们填满除记录推进以外的整个周期，便已经省去了所有 `[m_k+2,j_(k+1))` 空档，实际预设了 B。欲由此完成证明，需要额外的反向覆盖不等式 `sum ell_k>=P-2N`，或一个确实迫使全部空档为空的动力学论证。本轮没有取得它。

这些恒等式仅定位缺口；不把它们的长度推论作为新的周期下界成果。

## 4. 有限集合匹配为何尚未形成置换

对固定的一个完整周期定义两个**完整平移类集合**：

```text
S = {[A_k]_v : 0<=k<N},
R = {[C_k]_v : 0<=k<N}.
```

这里 A 的类由白源 `j_k` 代表，C 的类由第二记录白读 `m_k+2` 代表；它们都具有一个唯一秩零相位。

**命题。** 对第 1 节任意字与任意增长前沿，`|S|=|R|=N`。对于任意 `k,l in Z`，

```text
[C_k]_v=[A_l]_v
<-> exists z in Z, l=k+1+zN and eta_k=0.             (M)
```

**证明。** `F(A_l)-F(A_k)=2(l-k)`，而沿 v 平移 z 次改变高度 `2zN`，所以在 N 个连续下标内，A 的类不重复；C 同理。若 `A_l=C_k+zv`，比较高度得 `l=k+1+zN`。周期平移又给出 `A_l=A_(k+1)+zv`，故 `A_(k+1)=C_k`。反向直接使用周期平移。证毕。

因此，若一个周期中有 d 个非零滑移，则 `|S intersect R|=N-d`，双方各恰有 d 个未匹配类。**同基数不保证这两集合相等。** 每个前导黑读与自身白源之间的匹配是正确的，但白源未必来自 R；把它说成 R 上的置换，恰好遗漏了“像落在 R 中”的证明。若补得 `S=R`，由 (M) 已经得到 B。

固定有向边的稳定保序仍然有效，但它只匹配指定源类与指定方向的端口，不提供 `S=R`。见 [DriftRank.lean:783](D:/langtonsant/DriftRank.lean:783)。

## 5. 零净滑移、周期势函数与对角性

对任意 `k0 in Z` 定义

```text
H_F = sum_(k=k0)^(k0+N-1) eta_k.
```

位置望远镜求和得到上一轮的精确公式

```text
v=N*u+H_F*t,
2H_F=s1*a-s2*b.                                    (S)
```

由此有两个须区分的量词结论。

### 5.1 固定字、固定前沿

对所有满足第 1 节条件的 `(P,w,s1,s2)`，

```text
H_F=0 <-> s1*a=s2*b <-> v=N*(s1,s2).
```

B 蕴含这一结论。反向由 (S) 本身不能证明：整数滑移可以在代数上正负抵消。本轮**没有**构造一个真正自洽周期字来证明 B 与零净滑移在该模型内严格不等价。

### 5.2 全部字、全部增长前沿

以下两个全称命题等价：

```text
Z: forall P>0, forall w satisfying ConsistentWord P w,
     forall s1,s2 in {1,-1}, F(v)>0 -> H_F=0.

D: forall P>0, forall w satisfying ConsistentWord P w,
     if v=(a,b), then a^2=b^2.
```

`Z -> D`：非零 v 总有一个增长前沿，例如按坐标符号选择系数；由固定前沿结论得 `v=N*u`。`D -> Z`：非零对角漂移只有一组系数使 F 严格增加，且该组满足 `s1*a=s2*b`，由 (S) 得零净滑移。证毕。

因此，零净滑移是非对角漂移排除的等价接口，不是已经从周期性自动获得的余额结论。

### 5.3 “周期势函数望远镜”中的循环假设

沿边界定义整数坐标

```text
X_k=s1*(A_k).x-k.
```

直接计算：

```text
X_(k+1)-X_k=eta_k,
X_(k+N)-X_k=s1*a-N=H_F.
```

X 是一个带增量 H_F 的仿射周期量；它不是已知 N 周期量。**先把 X 当作周期量再求和消去，已经假设了 H_F=0。**

可以无条件构造真正周期量 `Y_k=N*X_k-k*H_F`，但此时

```text
Y_(k+N)=Y_k,
Y_(k+1)-Y_k=N*eta_k-H_F.
```

它的周期和只是 `N*sum eta_k-N*H_F=0`，不能产生新约束。用漂移法向坐标建立有界势函数也不能直接消去该常数；法向本身依赖尚未知的 v。

## 6. refute / verify：对抗检查

### 6.1 最强的周期内反证：标准字的边界接触并不单调

标准原相位 `P=104,v=(-2,-2)`，取 `F=-x-y`。前导黑读依次为 `m=21,31,125`。对 `m=31 -> 125`，旧最高层为 9，**全部**接触如下：

| 时间 | 位置 | 相对 C 的切向系数，t=(-1,1) | 稳定秩 |
| --- | --- | --- | --- |
| 33 | (-3,-6) | 0 | 0 |
| 39 | (-2,-7) | -1 | 0 |
| 49 | (-1,-8) | -2 | 0 |
| 109 | (-5,-4) | 2 | 0 |
| 119 | (-4,-5) | 1 | 0 |
| 125 | (-3,-6) | 0 | 1 |

该表已由本轮临时 Lean 定理 `standard_boundary_word` 用 `decide +kernel` 核验，包括完整接触时间列表、位置、稳定秩和截止时间 125 的高度上界。标准字自洽性使用仓库已有的 `Drift.standard_word_nonvacuous`，不是由本表推断。

结论：

- 第一重复的来源确实是第一个接触，故本例**满足 B**。
- 但在这次返回内部，存在四个其他首次白读的边界格，偏移分布在 C 两侧，时间顺序不是空间单调顺序。
- 这些四个格不是同一前沿任何记录黑读的物理来源：高度 9 对应的下一次突破只有本次，且本次选择的是 C。不能将全部边界白读视为必须逐一服务的记录来源。
- 它直接否定“只有一个边界白读”“接触单调”“必须选择最后接触”等通用桥梁；这些桥梁在真正周期白背景中也不成立。

这比仅在暂态找到反例更强，但它不反驳正确目标 rho=0。

### 6.2 同一前沿的相反滑移：补充已有暂态反例

对全白初态、原点朝北，取 `F=-x+y`、`t=(-1,-1)`：

| 前导黑读 m -> 下一前导黑读 | 下一白源 j | C | 下一 A | eta | delta |
| --- | --- | --- | --- | --- | --- |
| 4 -> 78 | 70 | (-1,1) | (1,3) | -2 | 64 |
| 78 -> 102 | 86 | (0,4) | (-1,3) | 1 | 6 |

第一行已由 [RecordSupportExamples.source_link_fails](D:/langtonsant/RecordSupportExamples.lean:112) 覆盖。本轮新增临时内核检查第二行的真实来源 `FirstSupportAt blank 86 102`、下一记录 103，以及区间 `[80,102]` 的高度不超过 4，保证没有遗漏中间记录对。

两段的完整边界接触时间分别是 `[6,12,22,70,78]` 与 `[80,86,102]`，前末接触全部不同；末次分别重复第四项与第二项，故选择指标 rho 分别为 3、1。

它否定仅由白首读、同向到达、来源唯一和同前沿分离推出统一 `eta>=0` 或 `eta<=0` 的论证。两段均是真实有限支撑轨迹，**但处于暂态**；没有反驳“仅在周期尾上成立”的单侧滑移命题或 B。

已有不同前沿支撑 `[0,4]` 与 `[1,53]` 的交错反例仍保留。本轮未把跨前沿区间假设为层叠，也未将它们合并求秩。

### 6.3 标准字任意幂、移相及旋转

解析上，替换 `(P,v)` 为 `(nP,nv)`，`n>=1`，并不改变双向物理轨迹。完整类会细分，但一个物理格的全部访问及首次返回相邻秩不变；记录接触字重复 n 次，`sum eta`、`sum ell`、`sum delta` 都相应重复。四分之一旋转及整数时间移位只运输这些对象。因此正规形、(T)、(M)、(S) 对任意幂和旋转保持有效，不要求最小周期。

独立 Python 诊断实际运行了：`n=1,2,3,4` 的全部 104 个移相与四种旋转，以及 `n=8,16,31` 固定相位的四种旋转，共 **1676** 个实例、**359160** 次相邻秩首次返回检查，全部通过。检查内容包括完整白首读奇偶、全部中间物理位置不回访、固定有向边的时间补偿、全部边界接触正规形、时间预算以及零滑移。

该数量是有限回归，不承担“任意 n”的证明。脚本从显式字重新计算坐标，负除数使用 Lean 风格欧几里得整除，不误用 Python 对负除数的向下取整。

### 6.4 跨周期提升与支撑预算

标准 `m=21` 的白源实际时间为 `33-104=-71`，支撑长度为 92；`m=31` 的白源为 23，支撑长度为 8。故

```text
N=2,  sum ell=92+8=100,  sum delta=0,
104=2*2+100+0.
```

特别是，6.1 的来源为 33，返回为 125，而不是简单比较相位 33 与 21。跨接缝的接触 109、119 同样保留为真实整数时间。最大相邻访问间隔仍为 116。所有固定边匹配均满足 `tau_succ-tau=1-P*liftStep`；全周期提升量和为 1，不把相位闭合当成物理闭合。

### 6.5 仅保留 incidence 的伪匹配会立即被拒绝

对标准字源类 `(0,0)` 的两条 W 出射，真实匹配 `4->5`、`92->93` 的稳定时间差均为 -103。交换成 `4->93`、`92->5` 后，差分别为 -15、-191。

交换保持类、方向与 incidence 数目，却不满足固定边统一时间补偿和有序匹配。因此不能把它用于构造正规形的真实实现，更不是 B 的自洽反例。

### 6.6 局部振荡子不提供耗尽论证

本轮重新独立执行了 Jillhewar 的单列振荡子：列 x=0 的黑格行初始为 `{1,2}`，从 `(0,2)` 朝 E 进入，读 `LR` 后得到 `{1,3}`，从 `(1,3)` 朝 E 离开；由外部重新指定从 `(0,2)` 朝 W 进入，读 `RL` 后恢复 `{1,2}`，从 `(-1,3)` 朝 W 离开。

它只展示合法局部颜色交替可以循环；外部两段之间的连接未给出。本文不把它当公路，也不使用“每一段探索都耗尽有限资源”排除 delta 空档。来源为 [Jillhewar 固定版本 rem:width4](https://raw.githubusercontent.com/Atharva12456/langtons-ant-highway/76a7e234e577d992d086c204c3dea00ae72cf10a/paper/main.tex)。

## 7. 与 Jillhewar / Ke 及上一轮的区别

Ke 的单位完整对角排除使用每个横向层恰有一个完整平移类、固定边保序和物理首次返回秩相邻。本题的增长层 `F(v)>0` 不具有该商空间几何。本文没有扩大其排除范围，也没有重做增长量或周期下界。参见 [Ke 固定版本的单位对角解析证明](https://raw.githubusercontent.com/kehao95/langtons-ant-core/b3429c25c33519c14f58f0a7171a857092bbd4cc/wake_synthesis/verification/unit_diagonal_analytic/PROOF.md)。

Jillhewar 的极值线、宽度排除和局部振荡子约束不等于本题的“首次重复选择第一项”。他的固定版本仍将周期分类列为开放问题；本文亦不以局部单列性质代替全轨迹可实现性。参见 [Jillhewar 固定版本 prob:periodic / rem:width4](https://raw.githubusercontent.com/Atharva12456/langtons-ant-highway/76a7e234e577d992d086c204c3dea00ae72cf10a/paper/main.tex)。

上一轮已得到滑移恒等式及跨类合并保序反例。本轮增加的是：**边界首次重复的精确选择指标、分离与覆盖之间的非负时间空档、两个秩零类集合之间缺失的像包含关系，以及标准周期内部非单调边界接触的内核见证。** 不主张这些初等推导在全部文献中具有新颖性。

## 8. 可先实现的最小 Lean 引理与本轮核验

适合先加入来源工具层的最小引理是：若某区域在一个时间前缀中的所有读取都为白，则该区域内的访问时间到位置映射是单射。它不需要有限支撑，也不需要周期。结合第 2 节的边界白读证明，可机械建立边界接触列表的互异性。

以下完整代码在临时文件中通过：

```lean
import DriftRank
import RecordSupportExamples

namespace LangtonsAnt.T1Research

theorem white_region_reads_injective (s : State) (region : Point -> Prop) (T : Nat)
    (hw : forall n, n < T -> region (run s n).pos -> readColor s n = false)
    {i j : Nat} (hi : i < T) (hj : j < T)
    (hri : region (run s i).pos) (hrj : region (run s j).pos)
    (hp : (run s i).pos = (run s j).pos) : i = j := by
  have noEarlier (n : Nat) (hn : n < T) (hr : region (run s n).pos) :
      forall r, r < n -> Not ((run s r).pos = (run s n).pos) := by
    apply white_reads_final_white_no_visit s (run s n).pos n
    · intro r hrn he
      exact hw r (by omega) (he.symm ▸ hr)
    · exact hw n hn hr
  by_cases h : i < j
  · exact False.elim (noEarlier j hj hrj i h hp)
  · by_cases h' : j < i
    · exact False.elim (noEarlier i hi hri j h' hp.symm)
    · omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem standard_boundary_word :
    ((List.range 93).map (fun i => i + 33)).filter
      (fun i => decide (linearForm (-1) (-1) (wordPos certifiedColor i) = 9)) =
        [33,39,49,109,119,125] ∧
    ([33,39,49,109,119,125].map (fun i => wordPos certifiedColor i)) =
      [(-3,-6),(-2,-7),(-1,-8),(-5,-4),(-4,-5),(-3,-6)] ∧
    ([33,39,49,109,119,125].map (fun i => Drift.stableRank 104 certifiedColor (i % 104))) =
      [0,0,0,0,0,1] ∧
    (forall i : Fin 126, linearForm (-1) (-1) (wordPos certifiedColor i) <= 9) := by
  decide +kernel

#print axioms white_region_reads_injective
#print axioms standard_boundary_word

end LangtonsAnt.T1Research
```

另一组检查使用以下已与 `packedBlank` 的实际运行核验相等的 106 字前缀：

```text
RRRRLRRRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRRRRLLLLRLLRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRRRRLLLLRLLRRRRLLRLRRR
```

具体过程是 `packedTrace packedBlank blank106=true` 经 `decide +kernel` 认证，再用 `packedTrace_sound` 与 `wordTrace_reads` 转为实际位置和读色；核验 `RunRecord (-1) 1 blank 103`、`pos 86=pos 102`、`readColor blank 102=true`，调用 `RecordSupportExamples.firstSupportAt_of_source` 获得 `FirstSupportAt blank 86 102`。完整接触列表与高度上界也用内核计算核验，没有只依靠 Python 模拟。

实际命令：

```powershell
$env:LEAN_PATH='D:/langtonsant/.lake/build/lib/lean'
& 'D:/langtonsant/tools/lean-4.36.0-windows/bin/lean.exe' -M1536 -DwarningAsError=true 'G:/TEMP/brainstorm2-t1-20261122-source-link/Checks.lean'
```

最终退出码为 0。`white_region_reads_injective` 的公理依赖为 `[propext, Quot.sound]`；`third_pair_source`、`transient_contacts`、`standard_boundary_word` 均为 `[propext, Classical.choice, Quot.sound]`。没有 `native_decide`、新增公理或 `sorryAx`。第一次草稿因误写布尔 `!=` 而非命题否定未通过；修正为 `Not (...)` 后全部通过，失败输出不作为证明。

这里使用仓库既有 `.olean`，未重建依赖。正规形整体、周期时间预算和集合匹配公式属于本轮纸面证明，**尚未端到端写成 Lean 定理**；上面的有限见证与最小辅助引理才是本轮实际内核核验范围。

## 9. 最终边界与下一步

本轮最精确的剩余义务有两个层级：

- **强版本 B：** 对所有自洽周期字、所有增长前沿和所有记录对，证明边界接触首次重复的选择指标 `rho_k=0`；等价地证明来源支撑达到 `(T)` 的覆盖等号，或秩零来源类集合 `S=R`。
- **弱版本：** 不必逐项链接，但要证明所选首次重复位置的有符号滑移总和为零。此命题等价于所有自洽周期字的完整漂移对角性，仍需新的全局约束。

现有局部来源与类内秩工具保证的是“选择真实存在且合法”，没有保证“选择第一项”；周期时间平移也没有保证支撑覆盖或切向势函数零增量。标准公路的额外边界接触已经排除了若干过强替代命题。

**诚实的不确定性：** B 可能对所有目标周期字成立，本轮没有否定它；本轮也没有证明存在非零滑移的自洽周期字、没有证明轴向或非对角漂移存在，更没有解决有限初态的最终周期性。没有进行未知周期字的完整搜索。

本轮仓库内仅新建本结果文件；未修改已有文件、未提交、未启动子代理、未执行 `lake build`。其他代理的并发修改不属于本轮产物。

**清理阻塞：** 实验仅在独立的仓库外目录 `G:/TEMP/brainstorm2-t1-20261122-source-link/` 进行。交付前已枚举确认该目录只有本轮的 `Checks.lean`、`explore.py`、`periodic.py` 三个文件，并校验绝对路径后请求删除；执行工具在启动命令之前拒绝了该请求，错误为 `approval required by policy, but AskForApproval::Granular.sandbox_approval is false`。未绕过该限制，因此这三个临时文件与目录尚未清理，需要协调线程或用户完成。此项不影响数学核验结果，但意味着“实验结束后删除”这一工作约束尚未完成。
