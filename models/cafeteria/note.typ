#import "../../typ/shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Optimal Departure Time and Walking Speed for the Cafeteria",
  date: "2026-09-01",
  tags: ("model"),
  summary: "Balancing departure time and walking speed for a cafeteria visit: jointly minimizing queueing time, food quality loss, and penalties for excessive speed.",
)

= Problem

Students may only use the cafeteria floor assigned to their grade. Choose a departure time $t$ and average speed $v$ to minimize the sum of walking and queueing time, food quality loss, and a penalty for walking too fast.

The model makes the following assumptions:

- Arrival times for students in this grade follow a shifted lognormal distribution;
- The cafeteria's maximum service rate is constant;
- Food neither runs out nor is replenished during service;
- Food quality decreases continuously and linearly with the cumulative number of people served;
- The queue is first-come, first-served, and no one leaves before being served.

= Arrivals and Queueing

Let $c$ be the earliest possible arrival time, and let $N$ be the total number of students in this grade dining on this floor. The cumulative distribution function of arrival times is

$ F(a) = cases(
  0, & a <= c,
  Phi((ln(a-c)-m)/sigma), & a > c,
). $

The corresponding density is

$ f(a) = 1/((a-c) sigma sqrt(2 pi))
  exp(-((ln(a-c)-m)^2)/(2 sigma^2)), quad a > c. $

Thus, the expected number of arrivals by time $a$ is $N F(a)$. The maximum density is

$ f_max = exp(-m + sigma^2/2)/(sigma sqrt(2 pi)). $

Let the constant service rate be $mu$. If $N f_max <= mu$, no queue forms. Otherwise, the queue begins to form at time

$ u = c + exp(m-sigma^2-sigma sqrt(2 ln((N f_max)/mu))). $

The time $e>u$ at which the queue clears is the nontrivial solution of

$ N(F(e)-F(u)) = mu(e-u) $

This equation generally has no elementary closed-form solution, but it can be solved using one-dimensional bisection. The queueing time for an arrival at time $a$ is

$ w(a) = cases(
  0, & a <= u,
  N/mu (F(a)-F(u))-(a-u), & u < a and a < e,
  0, & a >= e,
). $

= Food Quality

Normalize the initial food quality to $1$. Suppose that quality has decreased by a total of $eta$ after all $N$ people have been served. The quality after serving $n$ people is then

$ S(n) = 1-eta n/N. $

Under the first-come, first-served approximation, someone arriving at time $a$ has approximately $N F(a)$ people ahead of them, so their food quality loss is

$ 1-S(N F(a)) = eta F(a). $

= Relative Weights

The original penalty function is

$ J(t,v)
= alpha (d/v + w(t+d/v))
+ beta eta F(t+d/v)
+ gamma ((v-v_c)_+/v_c)^2. $

Multiplying $alpha,beta,gamma$ by the same positive constant does not change the optimum. Thus, when $alpha>0$, it suffices to consider two relative weights:

$ r_B = beta/alpha, quad r_V = gamma/alpha. $

After dividing the objective function by $alpha$, the function used in the computation is

$ J_"rel"(t,v)
= d/v + w(t+d/v)
+ r_B eta F(t+d/v)
+ r_V ((v-v_c)_+/v_c)^2. $

This eliminates redundant entries in the three-dimensional table of weights. The configuration file fixes the time weight at $1$ and lists the desired values of $r_B$ and $r_V$ separately for tabulation.

= Solution

Set the arrival time to $a=t+d/v$, and define

$ H(a)=w(a)+r_B eta F(a), $

$ C(v)=d/v+r_V ((v-v_c)_+/v_c)^2. $

Then $J_"rel"(t,v)=H(a)+C(v)$. Within the interval $u<a<e$ during which the queue exists,

$ H'(a) = (N/mu + r_B eta) f(a)-1. $

Interior stationary points satisfy

$ f(a) = 1/(N/mu+r_B eta). $

To find the optimal arrival time, it suffices to compare the endpoints of the allowed interval, the queue clearance time $e$, and any stationary points lying in $(u,e)$.

When $v>v_c$ and $r_V>0$, the optimal speed satisfies

$ 2 r_V (v^*)^2(v^*-v_c) = d v_c^2. $

This cubic equation has a unique solution for $v>v_c$; clamp that solution to the allowed speed interval. If $r_V=0$, choose the maximum allowed speed. The final output is

$ (t^*,v^*) = (a^*-d/v^*, v^*). $

= Parameters

#table(
  columns: (auto, 1fr),
  table.header([Parameter], [Meaning]),
  [$N$], [Total number of students in this grade dining on this floor],
  [$c$], [Earliest possible arrival time at the cafeteria],
  [$m$], [Mean of $ln(a-c)$],
  [$sigma$], [Standard deviation of $ln(a-c)$],
  [$mu$], [Number of people served per minute while a queue exists],
  [$d$], [Actual travel distance from the departure point to the cafeteria floor assigned to this grade],
  [$v_c$], [Comfortable walking speed],
  [$eta$], [Total proportional decrease in quality from the first customer to the last],
  [$r_B$], [Weight of the food quality penalty relative to the time penalty],
  [$r_V$], [Weight of the speed penalty relative to the time penalty],
)

The first eight quantities are obtained through observation or measurement; $r_B,r_V$ are freely chosen personal preferences. The two arrays in `params.example.toml` specify the combinations of relative weights to evaluate.

= Example Weight Table

The table below is populated automatically from `results.example.csv`, which is generated by the Rust program. Rows correspond to $r_B$ and columns to $r_V$; each cell lists the optimal departure time followed by the optimal speed (meters per minute).

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
