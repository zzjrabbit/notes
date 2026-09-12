#import "../../typ/shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "去食堂的最优出发时间与速度",
  date: "2026-09-01",
  tags: ("model"),
  summary: "食堂就餐的出发时间与速度权衡：排队等待、菜品质量损失与超速惩罚的联合最小化。",
)

= 问题

只能前往本年级对应的食堂楼层。选择出发时间 $t$ 与平均速度 $v$，使行走和排队耗时、菜品质量损失以及速度过快的惩罚之和最小。

模型采用以下假设：

- 本年级学生的到达时间服从一个平移对数正态分布；
- 食堂的最大服务率为常数；
- 菜品不会耗尽，也不会中途补充；
- 菜品质量随累计已服务人数连续、线性下降；
- 队列遵循先到先服务，且无人中途离开。

= 到达与排队

设 $c$ 为最早可能到达的时间，$N$ 为本年级在该楼层用餐的总人数。到达时间的分布函数为

$ F(a) = cases(
  0, & a <= c,
  Phi((ln(a-c)-m)/sigma), & a > c,
). $

对应密度为

$ f(a) = 1/((a-c) sigma sqrt(2 pi))
  exp(-((ln(a-c)-m)^2)/(2 sigma^2)), quad a > c. $

因此，到时间 $a$ 为止预计已有 $N F(a)$ 人到达。密度的最大值为

$ f_max = exp(-m + sigma^2/2)/(sigma sqrt(2 pi)). $

设恒定服务率为 $mu$。若 $N f_max <= mu$，则不会形成队伍。否则，队伍开始形成的时间为

$ u = c + exp(m-sigma^2-sigma sqrt(2 ln((N f_max)/mu))). $

队伍消失的时间 $e>u$ 是方程

$ N(F(e)-F(u)) = mu(e-u) $

的非平凡解。该方程通常没有初等闭式，用一维二分法求解即可。到达时间为 $a$ 时的排队时间为

$ w(a) = cases(
  0, & a <= u,
  N/mu (F(a)-F(u))-(a-u), & u < a and a < e,
  0, & a >= e,
). $

= 菜品质量

把初始菜品质量归一化为 $1$。设服务完全部 $N$ 人后，质量总共下降 $eta$，则服务 $n$ 人后的质量为

$ S(n) = 1-eta n/N. $

在先到先服务近似下，时间 $a$ 到达的人前面约有 $N F(a)$ 人，故其菜品质量损失为

$ 1-S(N F(a)) = eta F(a). $

= 相对权重

原始惩罚函数为

$ J(t,v)
= alpha (d/v + w(t+d/v))
+ beta eta F(t+d/v)
+ gamma ((v-v_c)_+/v_c)^2. $

同时将 $alpha,beta,gamma$ 乘以任意正常数不会改变最优解。因此，当 $alpha>0$ 时，只需研究两个相对权重

$ r_B = beta/alpha, quad r_V = gamma/alpha. $

将目标函数除以 $alpha$ 后，实际计算的是

$ J_"rel"(t,v)
= d/v + w(t+d/v)
+ r_B eta F(t+d/v)
+ r_V ((v-v_c)_+/v_c)^2. $

这消除了三维权重表中的重复项。配置文件固定时间权重为 $1$，分别列出希望制表的 $r_B$ 与 $r_V$。

= 求解

令到达时间 $a=t+d/v$，并定义

$ H(a)=w(a)+r_B eta F(a), $

$ C(v)=d/v+r_V ((v-v_c)_+/v_c)^2. $

于是 $J_"rel"(t,v)=H(a)+C(v)$。在队伍存在的区间 $u<a<e$ 内，

$ H'(a) = (N/mu + r_B eta) f(a)-1. $

内部驻点满足

$ f(a) = 1/(N/mu+r_B eta). $

最优到达时间只需在允许区间端点、队伍消失时间 $e$ 以及落在 $(u,e)$ 内的驻点之间比较。

当 $v>v_c$ 且 $r_V>0$ 时，最优速度满足

$ 2 r_V (v^*)^2(v^*-v_c) = d v_c^2. $

这是在 $v>v_c$ 上具有唯一解的三次方程；再将该解限制在允许速度区间内。若 $r_V=0$，则取允许的最大速度。最终输出

$ (t^*,v^*) = (a^*-d/v^*, v^*). $

= 参数

#table(
  columns: (auto, 1fr),
  table.header([参数], [含义]),
  [$N$], [本年级在该楼层用餐的总人数],
  [$c$], [最早可能到达食堂的时间],
  [$m$], [$ln(a-c)$ 的均值],
  [$sigma$], [$ln(a-c)$ 的标准差],
  [$mu$], [有队伍时每分钟完成服务的人数],
  [$d$], [出发点到本年级食堂楼层的实际路程],
  [$v_c$], [舒适行走速度],
  [$eta$], [从第一位到最后一位顾客的总质量下降比例],
  [$r_B$], [菜品质量惩罚相对于时间惩罚的权重],
  [$r_V$], [速度惩罚相对于时间惩罚的权重],
)

前八个量通过观察或测量获得；$r_B,r_V$ 是自由选择的个人偏好。`params.example.toml` 中的两个数组指定需要计算的相对权重组合。

= 示例权重表

下表由 Rust 程序生成的 `results.example.csv` 自动读取。行是 $r_B$，列是 $r_V$；每个单元格依次给出最优出发时间和最优速度（米/分钟）。

#let results = csv("results.example.csv", row-type: dictionary)
#let config = toml("params.example.toml")
#let quality-values = config.at("sweep").at("quality_over_time")
#let speed-values = config.at("sweep").at("speed_over_time")
#let cells = ()
#for (i, quality) in quality-values.enumerate() {
  cells.push([#quality])
  for (j, speed-weight) in speed-values.enumerate() {
    let row = results.at(i * speed-values.len() + j)
    cells.push([
      #(row.at("departure_clock")) \
      #(row.at("speed_display"))
    ])
  }
}

#table(
  columns: 1 + speed-values.len(),
  align: center,
  table.header(
    [$r_B backslash r_V$],
    ..speed-values.map(value => [#value]),
  ),
  ..cells,
)
