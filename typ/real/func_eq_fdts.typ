#import "/typ/shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Finite-Dimensional Translation Spaces and Lie Group Projections",
  date: "2026-08-14",
)

= The Start

This note starts with the following problem.
#example[
  Let $f: RR -> RR$ be a continuous function, which satisfies
  $ f(x+y)f(x-y)=f(x)^2-f(y)^2 $.
  Find all such functions.
]

I have the cover linear theorem in the Lie section for it.
But the conclusion of that theorem depends on the choice of
$G$, $pi$ and $Phi$, which weakens its power.

= The Climax

Thus, I wanted to find another approach. And I got the idea from the
standard solution:
Let $g_a (x) := (f(x+a)-f(x-a))/(2f(a))$.
Now, if we plug $f = sin$ into this expression,
after some calculations, we can get:
$ g = cos $.
The same can be done with $f = sinh$.

In the case of $f = sin$, $g = cos$, which gives us a circle
in a 2-dimensional space.
So, we can treat this equation as a projection of some
2-dimensional curve on $RR$.
More generally, most equations can be regarded as
a projection of a 1-dimensional manifold in a high dimensional space
on $RR$, and in which the curve can be one-parameterized by $RR$.

= The End
Finally, after chosing conditions which are strong enough to make conclusions,
we have the following theorem.

#theorem(title: "Finite-Dimensional Translation Space")[
  Let $f : RR -> RR$ be continuous and define its translation space
  $V_f = "span"_RR {tau_a f : a in RR}$, where $(tau_a f)(x) = f(x+a)$.

  If $dim V_f < infinity$, then:

  + $f$ is real analytic.
  + There exist distinct $lambda_1, dots, lambda_r in CC$ and nonzero polynomials $P_1, dots, P_r$ such that
    $ f(x) = sum_(j=1)^r P_j(x) e^(lambda_j x), $
    and moreover
    $ sum_(j=1)^r (deg P_j + 1) = dim V_f. $
    In particular, $r <= dim V_f$.
  + $f$ is a matrix coefficient of a one-parameter subgroup of $"GL"(V_f)$.
]

#proof[
  Let $T_a : V_f -> V_f$ be the restriction of the translation operator $tau_a$ to $V_f$.
  Since $V_f$ is invariant and finite-dimensional, $T_a in "GL"(V_f)$.

  The map
  $ rho : RR -> "GL"(V_f), quad rho(a) = T_a $
  is a group homomorphism:
  $ rho(a+b) = rho(a) rho(b), quad rho(0) = I. $

  It is continuous because for every $h in V_f$, the map $a |-> T_a h$ is continuous in the finite-dimensional topology of $V_f$.

  Hence there exists a unique $B in "End"(V_f)$ such that
  $ rho(x) = e^(x B) quad forall x in RR. $

  Define $L : V_f -> RR$ by $L(h) = h(0)$. Then
  $ f(x) = (tau_x f)(0) = L(tau_x f) = L(e^(x B) f). $

  Now $f$ is cyclic for $B$: since $V_f = "span"{e^(x B) f : x in RR}$, and $x |-> e^(x B) f$ is real analytic, its Taylor coefficients $B^k f$ span $V_f$.
  Therefore $V_f = "span"{B^k f : k >= 0}$.

  Complexifying $V_f$, the cyclic property implies the minimal polynomial of $B$ equals its characteristic polynomial.
  Thus each distinct eigenvalue $lambda_j in CC$ corresponds to exactly one Jordan block of size $s_j$, and
  $ sum_(j=1)^r s_j = dim V_f. $

  On the block for $lambda_j$, the matrix exponential contributes
  $ e^(lambda_j x), x e^(lambda_j x), dots, x^(s_j - 1) e^(lambda_j x). $

  Applying $L$ gives
  $ f(x) = sum_(j=1)^r P_j(x) e^(lambda_j x), $
  where $deg P_j = s_j - 1$. Hence
  $ sum_(j=1)^r (deg P_j + 1) = dim V_f. $
  Since $forall deg P_j + 1 >= 1$,
  $ r <= sum^r_(j=1) (deg P_j + 1) = dim V_f $

  Finally, $\{e^(x B) : x in RR\}$ is a one-parameter subgroup of $"GL"(V_f)$, and $f$ is its matrix coefficient.
]

Finally, as a sweet treat after our hard work, let us apply this theorem to solve the initial problem.

#solution[
  Let $g(x) := (tau_a f(x) - tau_(-a) f(x)) / (2 f(a))$, then $g in V_f$.
  Hence, $ f(x+y) + f(x-y) = 2f(x)g(y) $
  $ f(x+y) - f(x-y) = 2f(y)g(x). $
  Add them up, we obtain $ f(x+y) = f(x)g(y)+f(y)g(x) $,
  which is $ tau_y f = g(y) f + f(y) g $.
  Since $g in V_f$, $tau_y f in "span"{f,g} subset V_f$.
  Hence, $dim V_f <= 2$.

  By applying *Theorem 3.1*, we obtain
  $ f(x) = A e^(lambda x) + B e^(mu x) "or" (A+B x) e ^ (lambda x). $
  Substitute them into the original equation, we obtain
  $ f(x) = k x "or" f(x) = A sin (omega x) "or" f(x) = A sinh (k x) $
]

