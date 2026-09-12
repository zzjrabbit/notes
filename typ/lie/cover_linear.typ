#import "../shared.typ": *
#import "@preview/noteworthy:0.4.0": *
#import "@preview/cetz:0.5.2": canvas, draw

#show: tylenotes.with(
  title: "Cover Linear",
  date: "2026-08-11",
  tags: ("lie", "lean"),
  summary: "柯西型函数方程 f(xy)=f(x)+f(y) 在单调性假设下的解，以及向连续、可测等弱条件下的推广。",
)

= The Start

This note starts with the following problem.

#example[
  A function $f: (0, +infinity) -> R$ satisfies the following equation:
  $ f(x y) = f(x) + f(y) $.
  And $forall x > 1, f(x) > 0$, $f(2)=1$.
  Prove that $f(x)=log_2(x)$
]

#proof[
  Let $x = 1$, then $f(y) = f(1) + f(y)$, so $f(1) = 0$.
  Let $x = 1/y$, then $f(y * 1/y) = f(y) + f(1/y)$, hence $f(1) = f(y) + f(1/y)$.
  Therefore, $f(1/y) = - f(y)$.

  Let $0 < x_1 < x_2$, then $f(x_2/x_1) = f(x_2) + f(1/x_1) = f(x_2) - f(x_1)$.
  Since $0 < x_1 < x_2$, $x_2/x_1 > 1$, so $f(x_2/x_1) > 0$, and that $f(x_2) > f(x_1)$.
  So $f(x)$ is monotonically increasing on $(0, +infinity)$.

  $forall x in (0, +infinity) and n in NN, f(x^n)=f(x) * n$, so
  $f((2^(1/q))^q)=q * f(2^(1/q))$. Hence, $1/q f(2)=f(2^(1/q))$.
  Therefore, $f(2^(1/q))=1/q$.

  Let $q in QQ and q > 0$, then $exists a, b in NN, q = a/b$.
  Then $f(2^q)=f(2^(a/b)=a f(2^(1/b))=a/b f(2)=a/b=q$.
  So $forall q in QQ inter (0, +infinity), f(q)=log_2(q)$.
  Then by the density of $QQ$, we deduce that $f(x)=log_2(x)$.
]

= The Climax

The density of $QQ$ seems powerful, but it does not easily solve the following problem.

#example[
  $f(a)+f(b)=f(a+b/(1+a b)), a, b in (-1, 1)$
]

But this is clearly the functional equation for $arctan$.
So naturally we would like to prove that for "good enough" equations of this type, all continuous solutions differ at most by a constant; this is the following proposition.

#proposition[
  If an equation $F(x_i,f(x_i))=0$ satisfies certain "good enough" conditions, and if some "good enough" continuous function $f$ is a solution, then every solution can be written as
  $ A f(k_i x_i) $.
]

At first, I thought of the famous Cauchy equation:
$ f(x+y)=f(x)+f(y) $.
By adding "transformations" to this equation with some skills,
we may solve the equation above.

Then another natural thought is to study these transformations,
since we need at least one regularity condition to solve Cauchy's equation,
which is one of:
+ continuous
+ monotone
+ antitone
And we would need to study how these conditions are transformed by those transformations.

But after trying, I found that this might not be an interesting direction.
So I tried proving that for some limited kinds of functions,
*proposition 2.1* is true.
Thankfully, I was able to prove it when solutions need to be injective.

Yet the problem is not solved; for instance, consider the following.
#example[
  $ f(x) + f(y) = 2 f((x+y)/2) f((x-y)/2), x, y in RR $
]
The continuous solutions are cosines. Cosines are obviously not injective,
but we can handle it by setting $f(x)=cos(phi(x))$ and plugging it into the original equation.
Then I used DeepSeek to help me finish the final proof.
And that technique is in fact lifting to the covering space.

Anyway, here is what I obtained.

= The End

#theorem(title: "cover linear")[
  Suppose $f : RR -> RR$ is a non-constant continuous function,
  and there exists:
  1. A connected Lie group $G$.
  2. A continuous group homomorphism $Phi:RR -> G$ ( so $Phi(s+t)=Phi(s)Phi(t) and Phi(0)=e$ )
  3. A continuous mapping $pi: G -> RR$ (called a projection),
  such that the function $f$ can be represented as:
  $ f(x)=pi(Phi(x)) ( forall x in RR ) $
  
  Then there exists a unique Lie algebra element $frak(g) in "Lie"(G)$, such that 
  1. $phi(x) = p(exp(frak(g) x))$
  2. $f(x) = pi(p(exp(frak(g) x)))$
  3. For every continuous lifting $psi$ (a continuous mapping satisfying $p compose psi = phi$), it can be uniquely written as $ c * exp(frak(g) x) $, where $c$ lies in the kernel of the covering map: $p(c)=1_G$
]

#proof[
  Let $c$ = $psi_1(0) * psi_2(0)^(-1)$.
  $because$ p is a homomorphism $therefore$ $p(c) = phi(0) * phi(0)^(-1) = 1_G$
  $therefore$ $c in ker p$
  We obtain two mappings $RR -> tilde(G)$:
  1. $psi_1$
  2. $x |-> c * psi_2(x)$

  Both are continuous, and both equal $phi$ after projecting onto $G$. \
  Since left multiplication by kernel elements does not change the projection, and when $x = 0$, $psi_1(0)=c * psi_2(0)$,
  and since $RR$ is simply connected, by the uniqueness of covering liftings determined by base point and projection,
  we conclude that the two mappings must be equal everywhere. \
  Therefore, $psi_1(x) = c * psi_2(x)$.
  If there is another $c'$ also satisfying the conditions above, let $x = 0$, then
  $ c' = psi_1(0) * psi_2(0)^(-1) = c $
  Thus, c is unique.

  #canvas(length: 0.8cm, {
    import draw: *

    line((-4, 3), (4, 3), stroke: (thickness: 2pt, paint: rgb("#0055ff")))
    content((-4.5, 3.2), $tilde(G)$)
    circle((0, 3), radius: 0.15, fill: rgb("#ff0000"))
    content((0, 3.4), $tilde(e)$)
    circle((1.5, 3), radius: 0.1, fill: rgb("#0055ff"))
    content((1.5, 3.4), $exp(frak(g)x)$)

    circle((0, 0), radius: 2, stroke: (thickness: 2pt, paint: rgb("#8800aa")))
    content((2.8, 0.3), $G$)
    
    circle((2, 0), radius: 0.15, fill: rgb("#ff0000"))
    content((2.2, 0.3), $e$)
    
    let angle = 1.5
    let px = 2 * calc.cos(angle)
    let py = 2 * calc.sin(angle)
    circle((px, py), radius: 0.1, fill: rgb("#8800aa"))
    content((px + 0.3, py + 0.3), $Phi(x)$)

    let points_x = (-2, 0, 1.5)
    for x in points_x {
      let y_top = 3
      let angle_proj = x * 0.5
      let bx = 2 * calc.cos(angle_proj)
      let by = 2 * calc.sin(angle_proj)
      line((x, y_top), (bx, by),
           stroke: (dash: "dashed", thickness: 1pt, paint: rgb("#888888")),
           mark: (end: ">", fill: rgb("#888888")))
    }
    content((-2.5, 1.5), $p : tilde(G) -> G$, fill: rgb("#888888"))
  })


  Next we prove that $frak(g)_0$ is unique. Let another $frak(g)$ also satisfy the conditions,
  then it at least satisfies the first two, namely:
  1. $phi(x) = p(exp(frak(g) x))$
  2. $f(x) = pi(p(exp(frak(g) x)))$

  Since $RR$ is simply connected, and $p: tilde(G) -> G$ is a covering map,
  by the homotopy lifting property of covering spaces,
  for the continuous mapping $Phi : R -> tilde(G)$, there is
  $ p compose tilde(Phi) = Phi, tilde(Phi)(0) = tilde(e) $,
  where $tilde(e)$ is the identity element of $tilde(G)$ (because $p(tilde(e))=e$, we can fix the base point).
  For all $s,t in RR$, $
  p(tilde(Phi)(s+t) = Phi(s+t) = Phi(s)Phi(t) = p(tilde(Phi)(s))p(tilde(Phi)(s)) = p(tilde(Phi)(s)tilde(Phi)(t)) $
  Hence, $tilde(Phi)(s+t)$ and $tilde(Phi)(s)tilde(Phi)(t)$ are both liftings of the mapping $psi(u)=Phi(u)$
  at the point $s*t$.
  And since at the base point we have $tilde(Phi)(0)=tilde(e)$ and $tilde(Phi)(0)tilde(Phi)(0)=tilde(e)$,
  by the uniqueness of liftings we get $ tilde(Phi)(s+t) = tilde(Phi)(s)tilde(Phi)(t) $.
  So $tilde(Phi): RR -> tilde(G)$ is a continuous group homomorphism.

  The universal cover $tilde(G)$ is a simply connected Lie group.
  A continuous group homomorphism $RR -> tilde(G)$ is exactly a one-parameter subgroup of $tilde(G)$.
  By the fundamental theorem of Lie groups, there exists a unique $frak(g) in "Lie"(tilde(G))$ (Lie algebra),
  such that $ forall x in RR, tilde(Phi)(x) = exp(frak(g) x) $,
  where $exp : "Lie"(tilde(G)) -> tilde(G)$ is the exponential map.
  Hence, $ Phi(x) = p(tilde(Phi)(x)) = p(exp(frak(g) x)) $.
  Substituting the above result into $f = pi compose Phi$,
  we get $ f(x) = pi(p(exp(frak(g) x))) $.
  Now, under the exponential coordinate, the mapping $x |-> exp(frak(g) x)$ is simply the line $frak(g) x$.

  Thus, $frak(g)_0$ is unique.
]

This theorem is quite powerful, but not sufficient.
Because exam problems often do not provide continuity conditions,
we need the following corollary to handle such cases.

#corollary[
  If the solution of a functional equation must satisfy one of these conditions:
  1. continuous
  2. monotone
  3. antitone
  4. measurable
  Then its solution must be continuous, and can be solved by the theorem above.
]

#proof[
  By the theory of automatic continuity.
]

#note[
  In all the propositions above, $f: RR -> RR$ can be replaced by $f : X -> M$,
  where $X$ is a simply connected and locally compact Lie group,
  and $M$ is a topological space that is Hausdorff and second-countable,
  equipped with a Borel $sigma$-algebra.
]

The theorems above are really strong;
they tell you what "good enough" means,
and they are essentially a precise version of *proposition 2.1*,
though with a slight difference: it is not a difference of constants,
but rather a difference of constant Lie algebra elements.

Anyway, they can solve these problems easily, and here is an example.

#example[
  Let $f : RR -> RR$, and
  $ f(x+y) f(x-y) = f(x)^2 - f(y)^2 $
  where $f$ is non-constant and continuous.
  Find all such functions $f$.
]

#solution[
  By assumption, $f$ is non‑constant and continuous, so the corollary guarantees the required automatic continuity.  
  Hence we may apply the *cover linear* theorem.  
  There exists a connected Lie group $G$, 
  a continuous homomorphism $Phi : RR -> G$, 
  and a continuous projection $pi : G -> RR$ with
  $ f = pi compose Phi $.
  The theorem yields a unique element $frak(g)$ in the Lie algebra of $G$ such that
  $ Phi(x) = p(exp(frak(g) x)) $,
  $ f(x) = pi(p(exp(frak(g) x))) $,
  where $p : tilde(G) -> G$ is the universal covering map.

  Because $f$ is real‑valued, the one‑parameter subgroup $exp(frak(g) x)$ lives in a $1$‑dimensional Lie group.  
  Up to isomorphism, the only connected $1$‑dimensional Lie groups are the additive group $RR$, 
  the circle group $"SO"(2)$, and the hyperbolic group $"SO"(1,1)$.  
  Consequently, after choosing a suitable coordinate on the target, 
  the map $x |-> pi(p(exp(frak(g) x)))$ can only be of the form
  $ f(x) = alpha x, quad f(x) = beta sin(omega x + phi), 
  quad f(x) = gamma sinh(omega x + psi), "or" quad f(x) = gamma cosh(omega x + psi). $

  Now impose the given functional equation
  $ f(x + y) f(x - y) = f(x)^2 - f(y)^2 $.
  Setting $x = y = 0$ gives $f(0)^2 = f(0)^2 - f(0)^2$, thus $f(0) = 0$.
  Setting $x = 0$ yields $f(y) f(-y) = -f(y)^2$. 
  Since $f$ is not identically zero, we obtain $f(-y) = -f(y)$; hence $f$ is odd. \
  \
  Using $f(0)=0$ and oddness, we eliminate the cosine and constant phase shifts:
  + In the additive case, $f(x) = A x$ is already odd and vanishes at $0$.
  + In the sine case, $f(0) = beta sin phi = 0$ forces $phi = 0$ (mod $pi$). 
  Oddness then selects $phi = 0$, giving $f(x) = B sin(omega x)$.
  + In the hyperbolic case, $sinh$ is odd and vanishes at $0$, while $cosh$ is even and non‑zero at $0$; 
  therefore only $f(x) = C sinh(omega x)$ survives.

  All three families indeed satisfy the original equation:
  $ A(x+y) * A(x-y) = A^2(x^2 - y^2) = (A x)^2 - (A y)^2 $,
  $ B sin(omega(x+y)) B sin(omega(x-y)) = B^2(sin^2(omega x) - sin^2(omega y)) $,
  $ C sinh(omega(x+y)) C sinh(omega(x-y)) = C^2(sinh^2(omega x) - sinh^2(omega y)) $.

  Therefore, the complete list of continuous non‑constant solutions is
  $ f(x) = a x, quad f(x) = b sin(c x), quad f(x) = d sinh(e x) $,
  with arbitrary real constants $a, b, c, d, e$ 
  (the linear case can be seen as the limit $c -> 0$ in the sine family or $e -> 0$ in the $sinh$ family, 
  but we keep them distinct for clarity).

  This solves the problem by reducing the functional equation, via the *cover linear* theorem, 
  to the classification of one‑parameter subgroups of $1$‑dimensional Lie groups.
]

