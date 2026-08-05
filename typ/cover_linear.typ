#import "shared.typ": *
#import "@preview/noteworthy:0.4.0": *
#import "@preview/cetz:0.5.2": canvas, draw

#show: tylenotes

#theorem(title: "cover linear")[
  Suppose $f : RR -> RR$ is a non-constant continuous function,
  and there exists:
  1. A connected Lie group $G$.
  2. A continuous group homomorphism $Phi:RR -> G$ ( so $Phi(s+t)=Phi(s)Phi(t) and Phi(0)=e$ )
  3. A continuous mapping $pi: G -> RR$ (so called a projection),
  so that the function $f$ can be represented as:
  $ f(x)=pi(Phi(x)) ( forall x in RR ) $
  
  Then there exists a unique Lie algebra element $frak(g) in "Lie"(G)$, so that 
  1. $phi(x) = p(exp(frak(g) x))$
  2. $f(x) = pi(p(exp(frak(g) x)))$
  3. $forall$ continuous lifting $psi$(which is a continuous mapping satisfying $p compose psi = phi$) can be uniquely written as $ c * exp(frak(g) x) $, where c is in the kernel of the coverage space: $p(c)=1_G$
]

#proof[
  Let $c$ = $psi_1(0) * psi_2(0)^(-1)$.
  $because$ p is a homomorphism $therefore$ $p(c) = phi(0) * phi(0)^(-1) = 1_G$
  $therefore$ $c in ker p$
  Obtain two mappings $RR -> tilde(G)$:
  1. $psi_1$
  2. $x |-> c * psi_2(x)$

  They are all continuous and they are both equal to $phi$ after projecting onto $G$. \
  Since left multiplicating kernel elements does not change the projection, and when $x = 0$, $psi_1(0)=c * psi_2(0)$,
  from $RR$ being single connected and a coverage lifting is uniquely determined by the base point and projection,
  we can know that the two mappings must be equal ever where. \
  Therefore, $psi_1(x) = c * psi_2(x)$.
  If yet another $c'$ also satisfies the conditions above, let $x = 0$, then
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


  Then we will prove that $frak(g)_0$ is unique. Let yet another $frak(g)$ which also satisfies the conditions,
  then it at lest satifies the first two, which is to say:
  1. $phi(x) = p(exp(frak(g) x))$
  2. $f(x) = pi(p(exp(frak(g) x)))$

  Since $RR$ is single connected, and $p: tilde(G) -> G$ is a coverage mapping,
  according to homotopy lifting in coverage space theory,
  for continuous mapping $Phi : R -> tilde(G)$, there's
  $ p compose tilde(Phi) = Phi, tilde(Phi)(0) = tilde(e) $,
  where $tilde(e)$ is the identity element of $tilde(G)$(Because $p(tilde(e))=e$, we can fix the base point.)
  $forall s,t in RR, $
  $ p(tilde(Phi)(s+t) = Phi(s+t) = Phi(s)Phi(t) = p(tilde(Phi)(s))p(tilde(Phi)(s)) = p(tilde(Phi)(s)tilde(Phi)(t)) $
  Hence, $tilde(Phi)(s+t)$ and $tilde(Phi)(s)tilde(Phi)(t)$ are both a lifting of mapping $psi(u)=Phi(u)$
  at point $s*t$.
  And since that at the base point, we have $tilde(Phi)(0)=tilde(e)$ and $tilde(Phi)(0)tilde(Phi)(0)=tilde(e)$.
  From the uniqueness of lifting, we have $ tilde(Phi)(s+t) = tilde(Phi)(s)tilde(Phi)(t) $.
  So $tilde(Phi): RR -> tilde(G)$ is a continous group homomorphism.

  Universal coverage $tilde(G)$ is a single connected Lie group.
  Continuous group homomorphism $RR -> tilde(G)$ is exactly a one-parameter subgroup in $tilde(G)$.
  According to Li Group's Fundamental Theorem, there exists a unique $frak(g) in "Lie"(tilde(G))$(Lie algebra),
  so that $ forall x in RR, tilde(Phi)(x) = exp(frak(g) x) $,
  in which $exp : "Lie"(tilde(G)) -> tilde(G)$ is an exponential mapping.
  Hence, $ Phi(x) = p(tilde(Phi)(x)) = p(exp(frak(g) x)) $.
  Replace the result above into $f = pi compose Phi$,
  Then $ f(x) = pi(p(exp(frak(g) x))) $.
  Now that the mapping $x |-> exp(frak(g) x)$ is line $frak(g) x$ under exponential coordinate.

  Thus, $frak(g)_0$ is unique.
]

#corollary[
  If the solution of a functional equation must satisfy one of these conditions:
  1. continuous
  2. monotonous
  3. anti-monotonous
  4. Measurable
  Then it's solution must be continuous, and can be solved by the theorem above.
]

#proof[
  By the theory of automatic continuity.
]

#note[
  In all the propositions above, $f: RR -> RR$ can be replaced as $f : X -> M$,
  where $X$ is a single connected and locally compact Lie group,
  $M$ is a topological space with T2 and second countability
  and there is a Borel $sigma$-Algebra.
]

#example[
  Let $f : RR -> RR$, and
  $ f(x+y) f(x-y) = f(x)^2 - f(y)^2 $
  where $f$ is non-constant and $f$ is continuous.
  Find all kinds of $f$.
]

#solution[
  By assumption, $f$ is non‑constant and continuous, so the corollary guarantees the required automatic continuity.  
  Hence we may apply the *cover linear* theorem.  
  There exist a connected Lie group $G$, 
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
  quad f(x) = gamma sinh(omega x + psi), quad "or" quad f(x) = gamma cosh(omega x + psi). $

  Now impose the given functional equation
  $ f(x + y) f(x - y) = f(x)^2 - f(y)^2 $.
  Setting $x = y = 0$ gives $f(0)^2 = f(0)^2 - f(0)^2$, thus $f(0) = 0$.
  Setting $x = 0$ yields $f(y) f(-y) = -f(y)^2$. 
  Since $f$ is not identically zero, we obtain $f(-y) = -f(y)$; hence $f$ is odd. \
  \
  Applying $f(0)=0$ and oddness eliminates the cosine and constant phase shifts:
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

