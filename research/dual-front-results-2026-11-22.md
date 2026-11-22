# 双记录前沿：推广失败步骤与可复核的时序审计

日期：2026-11-22。任务：`research/dual-front-task-2026-11-22.md`。

## 0. 交付类型与结论边界

**本次达到结果 3：准确定位推广失败的步骤。** 没有证明全部非对角完整漂移不可能，也没有证明全部轴向完整漂移不可能；没有找到满足全部白背景自洽条件的非对角反例。

定位如下：`LangtonsAnt.Drift` 的首次物理返回、稳定秩相邻和固定有向边保序匹配均可继续使用。失败发生在将这些**逐完整平移类、逐有向边**的结论拼成**整条记录前沿或两条记录前沿**的统一匹配时。相邻记录对之间仍存在未受控制的沿前沿位移。把它删除，等价于额外假定来源链接；把不同类的端口合并后继续保序，则是被标准公路直接否定的命题。即使得到商图上的闭环，还必须保留绕数，不能把商闭合误作物理闭合。

本文给出三项可复核成果：

1. 对任意增长前沿，证明“同前沿高度且同完整平移类”当且仅当“同一物理位置”，并在临时 Lean 文件中完成纯内核核验。它精确暴露来源链接所缺的假设。
2. 写出逐记录对的横向滑移及其完整周期恒等式，定位待消去的量，而非仅说“缺少全局信息”。轴向时两套滑移总量均可为正，代数并不迫使相消。
3. 在真实标准公路上纯内核核验一个“相同出射方向、不同源类，合并排序后后继逆序”的具体反例，直接反驳跨类无条件保序这条候选桥梁。

这里没有证明某个形式公理系统的不可推导性。保留全部几何相位与 `ConsistentWord` 本身已经保留原问题的实质；本文只识别具体错误推理及仍待证明的连接命题。

## 1. 精确假设、量词和时间约定

取任意自然数 `P > 0` 及转向字 `w : Fin P -> Bool`，白读为 `false = R`，黑读为 `true = L`。调用仓库的 `ConsistentWord` 等接口时，将该有限字按模 `P` 周期延拓为 `Nat -> Bool`，仍记为 `w`。起始朝北，仅用于与仓库接口一致。设：

- 一个周期后朝向恢复；
- 完整周期位移为 `v = (a,b) != (0,0)`；
- `ConsistentWord P w` 成立，即每个完整平移类的稳定访问按秩从零开始读取 `R,L,R,L,...`。

不假设周期最小，不约分完整位移，不限制周期、宽度、增长或初始黑格数。有限支撑状态 `s`、暂态 `T` 及 `HighwayFrom s T P v` 通过仓库的周期尾自洽判据进入上述接口；有限暂态和未读遗迹不能删除。本文未重新编译该判据。

令 `q_i` 为周期内相位位置，`0 <= i < P`。以整数时间定义几何延拓：

```text
t = k P + i,  k in Z,  0 <= i < P
x_t = q_i + k v
x_(t+P) = x_t + v.
```

这是几何和读取次序的延拓，不宣称在某个整数时间其整个双向尾迹棋盘具有有限支撑。每个固定物理格仅有有限次相位访问；因此其首次访问及之前访问数是良定义的。对于真实有限支撑周期尾，可把任何有限检查窗口沿 `v` 平移到充分晚的副本，避开初始有限支撑及暂态足迹。

按 `DriftRank.lean:39-48` 定义：

```text
p ~v q  iff  exists z in Z, q = p + z v
ell_i = lift v q_i
c_i = base v q_i
tau_i = i - P ell_i
r_i = #{j < P : c_j = c_i and tau_j < tau_i}.
```

在物理格 `c_i + N v` 的访问时刻为 `N P + tau_j`，其中 `c_j = c_i`。跨相位零点、跨多个周期均使用这个整数式，禁止以相位编号大小代替物理先后。

后文所有 `r_t` 均指相位 `t mod P` 的稳定秩。它不是时刻 `t` 在整条轨迹中的序号，也不是某个有向端口子列表中的位置。

## 2. 保留精确 gadget 后确实得到什么

取任意 `s1,s2 in {1,-1}`，定义

```text
F(x,y) = s1 x + s2 y,   D = F(v) > 0.
```

整数时刻 `t` 是记录，指 `forall u < t, F(x_u) < F(x_t)`。因为 `F(x_t)` 向负时间趋于负无穷，记录定义合法。一个周期有恰好 `D` 次单位记录增量。朝向复原使 `P` 偶，从棋盘奇偶得 `a+b` 偶，故 `D` 偶。

记录到达方向使 `F` 增加。依据到达轴的奇偶性，记录层逐层交替为“右转继续增加”与“右转减少”；前一种记录紧接着产生下一层记录，故记录分成 `N = D/2` 对。可将全部记录对按整数时间索引为 `k in Z`，令前导黑读为 `m_k`，满足

```text
m_(k+N) = m_k + P.
```

上述记录计数是纸面推导，不是本轮新增 Lean 定理。它与 `RecordPair.lean` 中 `LangtonsAnt.pairStart_or_succ`、`LangtonsAnt.pairStart_step` 的逐层结构一致，不依赖有限周期枚举。

写 `A_k = x_(m_k)`，设 `e` 为 `m_k` 出射方向向量，`f` 为其右转向量，则 `F(e)=F(f)=1`，并且 `e+f=(s1,s2)`。完整局部轨迹为：

| 相对时刻 | 位置 | 读取 | 稳定秩 |
| --- | --- | --- | --- |
| `0` | `A_k` | L | 1 |
| `1` | `A_k+e` | R | 0 |
| `2` | `A_k+e+f` | R | 0 |
| `3` | `A_k+f` | R | 0 |
| `4` | `A_k` | R | 2 |
| `5` | `A_k+e` | L | 1 |
| `6` | `A_k+e-f` | 未由此局部因子指定 | 未指定 |

存在唯一 `j_k < m_k`，使 `x_(j_k)=A_k`；它是该物理格在 `m_k` 之前的唯一访问，读取 R，且到达朝向与 `m_k` 相同。因此 `r_(j_k)=0`、`r_(m_k)=1`，`[j_k,m_k]` 是真实首次返回。随后 `[m_k,m_k+4]` 和 `[m_k+1,m_k+5]` 也分别是首次返回。其秩增量均恰为一。

证明依据是 `RecordSupport.lean` 中 `LangtonsAnt.record_black_has_first_return`、`RecordPair.lean` 中 `LangtonsAnt.record_pair` 与 `LangtonsAnt.Drift.path_firstReturn_rank`；在整数周期形式下使用充分晚的同一窗口副本。三个新格的秩零来自记录之前不可达到对应高度及局部格点互异。没有把黑读的秩一弱化为任意奇数秩。

这一局部表已经完全兼容固定边保序：`A_k` 秩 1、2 的两次沿 `e` 出射，分别到达 `A_k+e` 秩 0、1。**保序匹配保留端口子列表的序号，并不保留两端完整类的数值秩。** 局部表自身没有矛盾。

## 3. propose：把缺失的来源链接写成可检验命题

记上一记录对的第二个新记录格为

```text
C_k = x_(m_k+2) = A_k + (s1,s2).
```

下一记录对的黑读基点 `A_(k+1)=x_(j_(k+1))` 与 `C_k` 位于同一前沿高度：

```text
F(A_(k+1)) = F(C_k) = F(A_k)+2.
```

由同前沿来源顺序及单位步长，`j_(k+1) >= m_k+2`。从 `m_k+2` 到 `j_(k+1)` 的整段路径位于 `F <= F(C_k)` 中，起终点均是各自物理格的首次读取。端点可以是同一条高度线上的不同格点。

候选连接命题 `B` 的完整量词为：

> 对所有 `P>0`、所有白背景自洽朝向复原字 `w`、所有 `s1,s2 in {1,-1}` 且 `F(wordDrift P w)>0`，以及上述双向记录对索引中的所有 `k in Z`，成立 `SameClass v C_k A_(k+1)`。

**`B` 尚未证明。** 它不是已有保序匹配定理的改写。

### 3.1 精确断点：相同前沿高度不能替代完整类相同

本轮证明并作纯内核检查的最小引理为：

> 对所有整数 `s1,s2`、所有 `v,p,q in Z^2`，若 `F(v) != 0` 且 `F(p)=F(q)`，则 `SameClass v p q <-> p=q`。

证明：若 `q=p+zv`，取 `F` 得 `0=zF(v)`，整数无零因子推出 `z=0`，故 `p=q`。反向取 `z=0`。

因此在此处，`B` 等价于 `C_k=A_(k+1)`。由于 `C_k` 在时刻 `m_k+2` 首次读取，`A_(k+1)` 在时刻 `j_(k+1)` 首次读取，物理位置相同进一步等价于

```text
j_(k+1) = m_k+2.
```

如果 `B` 成立，则每对推进 `(s1,s2)`，周期求和立即给出 `v=N(s1,s2)`。这确实足以迫使漂移对角，但**全部难点正好被塞进了 `B`**。仅凭“同一旧前沿”“两端都秩零”“支撑首次返回”或“相应边上保序”均没有提供 `B` 所需的跨类位置等式。

另一个纯内核核验命题是：当 `F(v)!=0` 时，对每个 `p`，`p ~v p+v`，但 `F(p)!=F(p+v)`。故增长前沿 `F` 根本不能直接下降为完整平移商上的高度函数。单位对角证明的横向层则满足 `F(v)=0`；这两种“层”不可混同。

### 3.2 未被消去的变量：沿前沿滑移

因为 `F(A_(k+1)-C_k)=0`，存在唯一整数 `eta_k` 使

```text
A_(k+1) = C_k + eta_k (s1,-s2)
          = A_k + (s1,s2) + eta_k (s1,-s2).              (1)
```

`eta_k=0` 正是来源链接。对任何实际满足上述假设的字，一周期求和给出

```text
H_F = sum_(k=k0)^(k0+N-1) eta_k
v = N(s1,s2) + H_F(s1,-s2)
N = (s1 a+s2 b)/2,       H_F = (s1 a-s2 b)/2.           (2)
```

这里 `k0` 任意，`eta` 是周期为 `N` 的整数序列。式 (1)、(2) 是保留位置信息之后的精确恒等式；它们本身没有证明 `eta_k=0`、`H_F=0` 或二者的任何有利符号。不能将它们包装成漂移排除定理。

### 3.3 两个前沿并不自动使滑移相消

假设 `a^2 != b^2`，置 `sigma=sign(a+b)`、`rho=sign(a-b)`、`epsilon=sigma*rho`。对任务中的两条增长前沿，式 (2) 化为

```text
N_plus  = |a+b|/2,       H_plus  = sigma(a-b)/2 = epsilon N_minus
N_minus = |a-b|/2,       H_minus = rho(a+b)/2   = epsilon N_plus.   (3)
```

两个 `N` 都正。横向滑移系数相对于各自指定的切向量计量，不能把两个不同切向量混成同一坐标轴后宣称相消。

尤其对任意完整轴向位移 `v=(a,0)`、`a>0`，朝向复原迫使 `a` 偶，而 (3) 给出

```text
N_plus=N_minus=a/2,      H_plus=H_minus=a/2.
```

两套几何恒等式是相容的。若要排除轴向，须证明这种正滑移需求与真实白首读历史及两套边界连接不能共存；目前的类内秩和固定边匹配没有给出这一步。没有声称式 (3) 可由某个轴向白背景周期字实现。

## 4. refute：两个不能使用的拼接捷径

### 4.1 固定有向边保序不能跨源类合并

仓库定理的精确前提是：对固定完整源类 `c` 和固定方向 `d`，所有 `i,j` 属于 `departures v P w c d`，才有

```text
tau_i < tau_j  iff  tau_(succ i) < tau_(succ j).
```

原因是每条这样的边都有同一个常数

```text
tau_(succ i) - tau_i = 1 - P * liftStep v c d.           (4)
```

“出射方向相同”而源类不同并不足够。标准 `P=104`、`v=(-2,-2)` 给出以下纯内核认证实例：

```text
outDir(2)=outDir(0)=W
base(q_2)=(1,1),       base(q_0)=(0,0)
tau_2=-102 < tau_0=0
tau_3=-101 > tau_1=-103.
```

两条 W 边的 `liftStep` 分别为 0、1。源排序合并后后继确实逆序，不是数值精度或相位零点问题。该例否定无条件的跨类合并保序；它只有一条增长前沿，故**不是**“两条增长前沿加全部自洽性”的反例。若希望利用第二条前沿恢复保序，必须另证一个使用双前沿的限制命题，不能删除固定源类前提。

改换每类代表也不能凭空补足该定理。若代表改为 `b'_c=b_c+h_c v`，相应稳定键变为 `tau'_i=tau_i+P h_c`，边提升量变为 `nu'=nu+h_c-h_target`。类内序不变，跨类比较却可改变；一个合法的全局排序论证必须说明其规范选择及边补偿。

### 4.2 商图闭环不等于零绕数物理返回

沿任意真实连续相位路径，若长度 `L>0`，提升后的端点相差 `delta v`，则已有通用定理给出

```text
tau_end - tau_start = L - P delta.                      (5)
```

只有物理端点相等，即 `delta=0`，才得到严格增加 `L`；若再证明无中间回访，才可用秩加一。

对普通完整周期的 `P` 条后继边，求和 (4) 得

```text
sum_i liftStep(v,c_i,outDir_i) = 1
0 = P - P*1.                                           (6)
```

这是非零漂移的正确相容恒等式。相位闭合处，物理位置前进了 `v`。对 `n` 周期同理为 `L=nP`、`delta=n`。

因此，候选“沿两套支撑和保序边走一圈，所有间隔为正，故矛盾”还欠两个独立义务：所有拼接边确实对应声称的连续路径或差分约束；以及整个闭环的提升量总和为零，或其完整权重和确实为正。不能只证明类或相位闭合。首次返回边本身 `delta=0`，并不意味着其间穿插的跨类转移也有零提升量。

这不是新增周期下界；它明确指出正环论证中不能省略的整数变量。

## 5. 单位对角证明的何处不能照搬

单位完整漂移 `(1,-1)` 下，横向层 `x+y` 同时满足：漂移不改变高度；每层只有一个完整平移类；每步高度变化为 `+1` 或 `-1`。由此才有极值单 R、邻层单一端口字及随后三层交错证明。

本任务的增长前沿满足 `F(v)>0`，不具备第一项，也不具备“同高度即同类”。取 `F(base v p)` 可人为得到类不变量，但单步增量成为

```text
F(moveVector d) - F(v) * liftStep(v,c,d),
```

不再是记录证明中的固定单位增量。对轴向 `v=(a,0)`，商空间是圆柱 `(x mod a,y)`，水平同层边仍存在；`y` 极值并不把全部相邻边都强制向内。换成真正的法向 `b x-a y`，一般非对角情形的步长也不是全为单位量，轴向还有零步长。

因而不能仅把 `UnitDiagonal` 命名空间替换为 `Drift`，就继续得到相同的极值端口字。通用秩工具完成的是时序接口，不是单位对角特有的层几何强制。

## 6. verify：自我对抗检验与明确结果

### 6.1 标准字任意幂、相位移位及空间旋转

纸面上，对任意 `n>=1`、任意四分之一转旋转 `R` 及任意整数时间移位，标准轨迹仍满足姿态周期 `(104n, n R(-2,-2))`。对角性保持，仍只有一条严格增长的对角前沿。

更一般地，将一个周期 `(P,v)` 改为 `(nP,nv)`，同一条实际几何轨迹不变。以 `nv` 取商会将旧完整类分成纵向余数子类；但每个固定物理格的全部访问时间及读取顺序不变，故合法首次返回仍连接相邻秩。不能在取幂后继续沿用模 `v` 的旧类，亦不能将新完整位移约分。记录对重复 `n` 次，横向滑移总量按 `n` 缩放；式 (1)--(6) 全部相容。

独立 Python 检查使用仓库 `StandardHighway.highwayWord` 的 104 个字母，从定义重新生成位置、朝向、完整类、Lean 风格欧几里得整除、稳定时间、全部有向边以及首次返回。运行了：

- `n=1,2,3,4`，全部 104 个循环相位移位，四种空间旋转；
- `n=8,16,31`，固定相位的四种空间旋转；
- 共 1676 个正向实例、359160 个相邻秩首次返回检查，全部通过。

这些有限实例不是任意幂结论的证明；任意幂的理由是上一段的同一实际轨迹论证。循环移位时，脚本以新的起始朝向重建轨迹，故可能伴随一次整体旋转，不把字移位和空间坐标系误当成独立不变数据。

标准原相位得到 22 个完整类、82 个相邻访问间隔，最大间隔 116。记录黑读来源为：

```text
m=21 : source phase 33, source time -71, interval 92
m=31 : source phase 23, source time  23, interval  8.
```

这直接检查跨周期提升。记录滑移为 `[0,0]`，与来源链接候选相容；不能据此证明未知周期字也满足该候选。

### 6.2 合法首次返回不是全局稳定时间单调

每个被检查的类按 `tau` 排序后，脚本逐一重放相邻访问间的全部物理整数时刻，确认没有遗漏对端点的中间访问；并核对所有有向边的后继双射和固定常数 (4)。本轮没有仅用“颜色相反”代替首次返回。

同时，所有标准实例的全周期提升量和为 1。故“每一合法返回增加秩”与“周期后继图存在一个环”没有直接矛盾。两者比较的对象不同。

### 6.3 `RecordSupportExamples` 的两项实际有限轨迹反例

对全白前 80 步重新模拟并核对：

- `F=-x+y` 的支撑 `[0,4]` 与 `F=x+y` 的支撑 `[1,53]` 真正交错：`0<1<4<53`。来源、朝向和唯一先前访问全部正确。
- `F=-x+y` 的相邻记录对起点为 5 和 79，下一来源为 70，而不是上一对第二记录时刻 6。`x_6=(-1,1)`、`x_70=(1,3)`；相对切向量 `(-1,-1)`，这里 `eta=-2`。

对应仓库纯内核声明为 `RecordSupportExamples.crossing_distinct_fronts`、`source_link_fails`。本轮没有重新构建这些文件；临时 Lean 检查导入了现有已构建模块。

第一项否定任意有限轨迹上的跨前沿层叠性；第二项否定仅凭局部记录与白源条件的来源链接。它们是有限暂态反例，**不否定仅在白背景周期尾上量化的命题 `B`**。本文保持这个量词差别。

### 6.4 已知单列局部振荡子

核对 Jillhewar 固定来源的 `rem:width4`，并独立执行其两个局部片段。固定列 `x=0`，初始列内黑格为 `{(0,1),(0,2)}`：

```text
从 (0,2) 朝 E 进入：L,R -> 列内黑行 {1,3}，从 (1,3) 朝 E 离开
外部重新从 (0,2) 朝 W 进入：R,L -> 列内黑行 {1,2}，从 (-1,3) 朝 W 离开。
```

两次被复用的格子正确交替读取，恢复列内状态，没有复用极值行。第二次入射由外部给定，未构造连接两段的全局轨道。因此这个振荡子只否定无条件的单列无环性；不能将其冒充轴向公路，也不能由局部循环反推全局可实现。反过来，本文没有使用“每个局部片段均严格耗尽有限资源”的未经证明前提。

### 6.5 incidence-only 伪匹配的负对照

从标准字真实数据保留各类、方向、访问次序及端口数量，只交换同一有向边上的两次目标出现：

```text
源类 (0,0)，方向 W
真实边：phase 4 -> 5，phase 92 -> 93
源 tau：-100，-12
目标 tau：-203，-115
伪交换：4 -> 93，92 -> 5。
```

伪交换保留入出度与相同方向的 incidence 数量，源和目标仍落在正确的完整类，但逆转稳定次序，而且其键差不再统一为 `1-104=-103`。它不满足真实相位后继，也不满足有序匹配，因此立即被拒绝。

这是用来防止把度数与颜色计数当成实现性的负对照，不是交付类型 2 的完整自洽反例。

### 6.6 44 步轴向无限背景例子的严格排除

重新检查字 `10000100100001011011001101010000100100001010`，使用朝北规范得到 `(P,v)=(44,(0,4))`。两套记录前沿和全部局部 `100001` 几何成立，有向边匹配与合法首次返回也成立；但四个记录前导黑读相位 `0,8,27,35` 的稳定秩全部为 0，不是 1。共 12 个相位违反白首读秩奇偶条件。

因此它没有黑读白源，必须依赖无限背景。仓库 `DualFrontCountermodel.not_consistent`、`not_finite` 已明确该边界。本轮绝不将它算作满足任务全部自洽条件的反例。它证明的仅是：通用几何时序工具和双 gadget 必须与白首读条件一起使用。

## 7. 与 Jillhewar / Ke 已知结果的关系

本轮再次读取以下固定版本的原始证明文本，没有运行外部代码：

- Jillhewar，提交 `76a7e234e577d992d086c204c3dea00ae72cf10a`，`paper/main.tex`：增长四的特殊漂移排除、宽度排除及单列振荡子。
- Ke，提交 `b3429c25c33519c14f58f0a7171a857092bbd4cc`，`wake_synthesis/verification/unit_diagonal_analytic/PROOF.md`：单位完整对角漂移的逐层有序匹配和首次返回证明。
- Ke，同提交 `wake_synthesis/paper/axis-wake.tex`：任意完整轴向位移的严格逆序偶性必要条件。

本结果没有扩大上述漂移排除范围，没有把 `g>=8` 或周期下界重新列为进展。与已有一般工具相比，本文增加的是**本候选的失败接口审计**：增长前沿与完整类的不可互换性、横向滑移的精确余额，以及跨类合并保序的标准字核验反例。

Ke 的轴向逆序条件允许非空尾迹，也没有消去全部轴向候选。本次滑移恒等式与它不存在已证明的冲突；未对未知轴向候选声称通过了其全部筛选。

固定来源地址：

```text
https://github.com/Atharva12456/langtons-ant-highway/blob/76a7e234e577d992d086c204c3dea00ae72cf10a/paper/main.tex
https://github.com/kehao95/langtons-ant-core/blob/b3429c25c33519c14f58f0a7171a857092bbd4cc/wake_synthesis/verification/unit_diagonal_analytic/PROOF.md
https://github.com/kehao95/langtons-ant-core/blob/b3429c25c33519c14f58f0a7171a857092bbd4cc/wake_synthesis/paper/axis-wake.tex
```

## 8. 最小 Lean 引理、实际核验及复现材料

首个建议移入仓库的最小引理是 `sameClass_same_level_iff_eq`。它明确阻止错误调用跨类匹配；它不是轴向或非对角排除定理。以下是本轮在仓库外实际通过的完整检查代码，不含占位证明：

```lean
import DriftRank
import RecordSupportExamples

namespace LangtonsAnt.DualFrontResearchCheck

theorem linearForm_add_scale (s1 s2 : Int) (p v : Point) (z : Int) :
    linearForm s1 s2 (addPoint p (scalePoint v z)) =
      linearForm s1 s2 p + z * linearForm s1 s2 v := by
  simp only [linearForm, addPoint, scalePoint, Int.mul_add,
    Int.mul_left_comm]
  omega

theorem sameClass_same_level_iff_eq (s1 s2 : Int) (v p q : Point)
    (hv : linearForm s1 s2 v ≠ 0)
    (hpq : linearForm s1 s2 p = linearForm s1 s2 q) :
    LangtonsAnt.Drift.SameClass v p q ↔ p = q := by
  constructor
  · rintro ⟨z, hz⟩
    have hf := congrArg (linearForm s1 s2) hz
    rw [linearForm_add_scale] at hf
    have hzero : z * linearForm s1 s2 v = 0 := by omega
    have hz0 : z = 0 := (Int.mul_eq_zero.mp hzero).resolve_right hv
    subst z
    simpa [addPoint, scalePoint] using hz.symm
  · intro h
    subst q
    exact LangtonsAnt.Drift.SameClass.refl v p

theorem growing_front_not_class_invariant (s1 s2 : Int) (v p : Point)
    (hv : linearForm s1 s2 v ≠ 0) :
    LangtonsAnt.Drift.SameClass v p (addPoint p v) ∧
      linearForm s1 s2 p ≠ linearForm s1 s2 (addPoint p v) := by
  constructor
  · exact ⟨1, by simp [scalePoint]⟩
  · intro he
    apply hv
    simp only [linearForm, addPoint, Int.mul_add] at he ⊢
    omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem standard_cross_class_order_reverses :
    LangtonsAnt.Drift.outDir certifiedColor 2 = .west ∧
    LangtonsAnt.Drift.outDir certifiedColor 0 = .west ∧
    LangtonsAnt.Drift.stableTime (-2, -2) 104 certifiedColor 2 = -102 ∧
    LangtonsAnt.Drift.stableTime (-2, -2) 104 certifiedColor 0 = 0 ∧
    LangtonsAnt.Drift.stableTime (-2, -2) 104 certifiedColor 3 = -101 ∧
    LangtonsAnt.Drift.stableTime (-2, -2) 104 certifiedColor 1 = -103 ∧
    ¬ LangtonsAnt.Drift.SameClass (-2, -2)
      (wordPos certifiedColor 2) (wordPos certifiedColor 0) := by
  decide +kernel

#print axioms sameClass_same_level_iff_eq
#print axioms growing_front_not_class_invariant
#print axioms standard_cross_class_order_reverses

end LangtonsAnt.DualFrontResearchCheck
```

实际命令使用 Lean 4.36.0，读取仓库既有 `.olean`，未运行 `lake build`：

```powershell
$env:LEAN_PATH='D:/langtonsant/.lake/build/lib/lean'
& 'D:/langtonsant/tools/lean-4.36.0-windows/bin/lean.exe' -M1536 -DwarningAsError=true 'G:/TEMP/dualfront-research-20261122-5470/BridgeChecks.lean'
```

最终退出码 0。前两项公理依赖为 `[propext, Quot.sound]`；标准字反例为 `[propext, Classical.choice, Quot.sound]`。没有 `sorryAx`、自定义公理或 `native_decide`。第一次草稿检查曾因未使用 simp 参数及一个未展开的线性表达式失败，修正后以上完整代码通过；失败草稿不作为证明。

Python 属于诊断而非证明。其独立实现采用 `N,E,S,W` 四方向、白右黑左、先翻色再移动；先按 `c=q-lift(q)v` 分组，再按 `tau` 排序。负除数使用欧几里得商 `-(x // (-y))`，不误用 Python 对负除数的向下取整。每个相邻访问从 `tau_i` 到 `tau_j` 重放全部整数位置；每条边检查 (4) 及排序后的双射。其输出计数和关键见证已完整列在第 6 节，实验脚本本身不保留在仓库。

## 9. 后续真正需要证明的命题与工作边界

最直接但尚未成立的路径是证明候选 `B`，或更弱地证明在完整白背景周期内所有沿前沿滑移的净额必须为零。两者都须实质控制从 `C_k` 到下一来源 `A_(k+1)` 的非记录边界探索，不能通过丢掉这些访问达成。也可寻找两前沿耦合的带提升量差分不等式，但必须逐边证明匹配，保留所有类标签与绕数，并证明其总权重严格为正。

最强反证测试是第 4.1 节的真实标准字纯内核反例：连合法白背景周期轨迹也不满足跨类合并后的无条件保序。因此这条通用桥梁已被确实否定。最强尚未否定的候选是只对白背景周期尾量化的来源链接 `B`；本轮既没有证明它，也没有构造反例。

本次只新增本 Markdown 文件；未修改已有文件，未提交，未启动子代理，未构建 `SingleBlack*` 或 `PeriodicNative`。实验位于仓库外的独立临时目录，并在交付前清理。本文嵌入的 Lean 代码可重建最小检查，但没有将它安装为仓库模块。

**最终状态：准确识别了“类内时序 → 跨前沿来源连接 → 零绕数矛盾”链条中缺失的连接及绕数义务；非对角排除、轴向排除和一般有限初态公路猜想均未被本次工作解决。**
