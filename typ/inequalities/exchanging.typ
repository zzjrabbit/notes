#import "../shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Exchanging Exponentials",
  date: "2026-09-14",
  tags: ("inequalities"),
  summary: "When exponentials get larger by exchanging the two parameters",
)

= The Start

The problem we are discussing here can be formalized with the following proposition.
#proposition[
  Given $1 < a < b$, $a^b < b^a$ if and only if $f(a,b)>0$.
]
Here, the map $f(a,b)$ is our purpose.

It is a natural thought to use exponentials like $a^a$ or $b^b$ to solve the problem.
However, this is not effective. Here is an example.
#solution[
  $a ^ a < a ^ b < b ^ b$, while $b ^ a < b ^ b$.
]
Hence we need some other tools, instead of pure inequalities.
Another natural thought to solve the problem, is to use the natural logarithm.
Thus the problem is asking when $e^(b ln(a)) < e ^ (a ln(b))$ is true,
which is in fact simply $b ln(a) < a ln(b)$.
It is a simple matter to see that this is equivalent to $a / b < ln(a) / ln(b)$.
However, you can't see how can this solve the problem.
A traditional way is to rewrite the inequality like the following:
$ ln(a) / a < ln(b) / b. $
The next step is to let $f(x) := ln(x) / x$,
and study the property of this function on the interval $(1, +inf)$.
This, as you can see, is pretty boring. After drawing many pictures,
which filled half of my crafts, I discovered the following, which is much more interesting.

= The Climax

We have already shown that the original problem is equivalent to find
when the equality $a / b < ln(a) / ln(b)$ holds.
Let's draw a picture of $x |-> x$ and $x |-> ln x$ on a same figure.
Hence we are actually comparing the the slope of the line passing through $(a, ln(a))$ and $(b, ln(b))$.
Since these are lines, we may let the one through the points $(a, ln(a))$ and $(b, ln(b))$
be $y = m * x + n$. By Karamata's inequality, we know that the original
inequality holds if and only if $n < 0$.

= The End

The following theorem is the final result of this note.

#theorem[
  Given $1 < a < b$, $a^b < b^a$ if and only if $a < e ^ ((ln(k))/(k-1))$, where $k=b/a$
  And the inequality never holds if $a >= e$.
]

#proof[
  First proof that $a^b < b^a => a < e^(ln(k) / (k-1))$.
  Since $a^b < b^a$, we obtain $e^(b ln(a)) < e^(a ln(b))$.
  By the results above, we have $ a/b > ln(a) / ln(b). $
  Set points $A(a, ln(a))$ and $B(b, ln(b))$ in a plane.
  Let the line through $A$ and $B$ be $y = m x + n$.
  It is clear that $A(a, m a + n)$, $B(b, m b + n)$.
  Thus, by Karamata's inequality, the original inequality holds if and only if $n<0$.
  So we only need to prove that $n < 0$ if and only if $a < e^(ln(k)/(k-1))$.
  Substitute the position of $A$, $B$ into $"AB": y = m x + n$, we obtain
  $ m = ln(a) - ln(b/a)/(b/a - 1). $
  Let $k = b/a$, then $m = ln(a) - ln(k)/(k-1)$. Thus, $a < e^(ln(k)/(k-1))$.

  Finally, we prove that the inequality never holds if $a >= e$.
  It is obvious that $ln(k) <= k-1$. Clearly, since $b > a$, $k > 1$.
  Thus we obtain $ln(k)/(k-1) <= 1$.
  Hence, unless $a < e$, otherwise the inequality is false,
  which is equivalent to our goal.
]

