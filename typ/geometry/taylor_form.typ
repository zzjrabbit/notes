#import "@preview/noteworthy:0.4.0": noteworthy
#import "../shared.typ": *

#show: tylenotes.with(
  title: "Taylor Form",
  date: "2026-10-30",
  tags: ("geometry", "lean"),
  summary: "Properties of so-called Taylor Forms, which are close to jet bundles.",
)

= The Start

The reason why I call this expression 
$sum_(i=0)^infinity a_i omega^i (dif omega)^k$,
where $omega$ is a smooth 0-form,
is not hard to see.
Then an interesting question is raised: does this form
act exactly like Taylor series, which only converges for certain kinds
of functions. In this case, that is to say, does this expression
converge only for certain kinds of differential forms?

== The Climax

It's obvious that by choosing certain $a_i$ and $k$
we can control the degree of this expression to be any non-negative number.
In addition, it is not hard to see that this proposition must not be true,
otherwise in the case of $RR$ this would immediately imply that
$C^omega (RR) = C^infinity (RR)$, which is obviously false.
The key is to calculate this expression in a smooth coordinate chart.
But for that we would have to study
$sum_(i=0)^infinity a_i phi^i$ first.
Hence, we have the following lemma.

#lemma[
  There exist no $x_0 in RR$ and no smooth function $phi$
  defined on a neighborhood of $x_0$ such that
  for any $f in C^infinity (RR)$,
  there exist some real numbers $a_i$ and a neighborhood $U_f$ of $x_0$
  with $f(x) = sum_(i=0)^infinity a_i phi(x)^i$ for all $x in U_f$.
]

#proof[
  Assume that such $x_0$ and $phi$ exist.
  Take $f(x) = x$. By hypothesis there exist $a_i$ and a
  neighborhood $U_1$ of $x_0$ with
  $x = sum_(i=0)^infinity a_i phi(x)^i$ on $U_1$.
  If $phi$ is constant on $U_1$, the right-hand side is constant,
  contradiction. If $phi$ is not injective on $U_1$, take
  $x_1 eq.not x_2$ in $U_1$ with $phi(x_1) = phi(x_2)$;
  the right-hand side takes the same value at $x_1$ and $x_2$,
  contradiction. Hence $phi$ is injective on $U_1$, so it is
  strictly monotone there. Let $I = phi(U_1)$ and
  $Phi = phi^(-1): I -> U_1$.
  If $phi'(x_0) = 0$, then $Phi$ cannot be differentiable at
  $y_0 = phi(x_0)$. But taking $f(x) = x - x_0$, we get
  $Phi(y) - x_0 = sum_(i=0)^infinity a_i y^i$
  on a neighborhood of $y_0$, so $Phi$ is real analytic there,
  contradiction. Hence $phi'(x_0) eq.not 0$, so $Phi$ is smooth
  near $y_0$.
  Now take a nonzero smooth function $f$ which is flat at $x_0$,
  i.e. $f^((j))(x_0) = 0$ for all $j in NN$. By hypothesis there
  exist $b_i$ and a neighborhood $U_2$ of $x_0$ with
  $f = sum_(i=0)^infinity b_i phi^i$ on $U_2$. On
  $U_1 inter U_2$ we have
  $f compose Phi = sum_(i=0)^infinity b_i y^i$, which is analytic
  near $y_0$. Since $f$ is flat at $x_0$ and $Phi$ is smooth,
  $f compose Phi$ is flat at $y_0$. An analytic function which is
  flat at a point vanishes identically near that point.
  Hence $f compose Phi equiv 0$ near $y_0$, so $f equiv 0$
  near $x_0$, contradiction.
  Thus no such $x_0$ and $phi$ exist.
]

Now, we are ready to prove the final theorem.

== The End

Throughout, a series of the form
$sum_(i=0)^infinity a_i omega^i (dif omega)^k$
is understood to converge locally uniformly together with all
termwise derivatives, so that termwise differentiation and
integration are legitimate.

#theorem[
  Let $M$ be a smooth manifold with $dim M >= 1$.
  It is impossible to find a smooth 0-form $omega$ such that
  $forall k in NN_+ "with" k <= dim M, forall f in Omega^k (M),
  exists a_i in RR$,
  such that $f = sum_(i=0)^infinity a_i omega^i (dif omega)^k$.
]

#proof[
  Assume that there exists some $omega in Omega^0 (M)$
  such that forall $k in NN_+$ with $k <= dim M$,
  $forall f in Omega^k (M), exists a_i in RR$,
  $f = sum_(i=0)^infinity a_i omega^i (dif omega)^k$.

  It suffices to take $k = 1$.
  Given a smooth chart $(U, phi)$,
  we consider the case of smooth 1-forms.
  Then $f$ on $U$ is $sum_(i=1)^n f_i dif x^i$,
  $dif omega$ on $U$ is
  $sum_(i=1)^n (partial omega)/(partial x^i) dif x^i$.
  For the ith coordinate, it follows that
  $f = sum_(j=0)^infinity a_j omega^j dif omega =>
  f_i = (partial omega)/(partial x^i) sum_(j=0)^infinity a_j omega^j$.
  We claim that $(partial omega)/(partial x^i)$ never vanishes on $U$.
  Indeed, for any $p in U$, take $chi in C_c^infinity (U)$ equal to
  $1$ near $p$ and set $f = chi dif x^i$; this is a global smooth
  1-form on $M$. Comparing the $dif x^i$ components on a neighborhood
  of $p$ gives
  $1 = (partial omega)/(partial x^i) sum_(j=0)^infinity a_j omega^j$,
  so $(partial omega)/(partial x^i)(p) eq.not 0$. Since $p$ is
  arbitrary, $(partial omega)/(partial x^i)$ is nowhere vanishing on $U$.

  Fix $x' = (x^1, dots, x^(i-1), x^(i+1), dots, x^n)$
  and $t_0$ with $(t_0, x') in U$. Take a cutoff function
  $chi in C_c^infinity (U)$ equal to $1$ near $(t_0, x')$, and
  write $t = x^i$. For any $h in C^infinity (RR)$, set
  $f = chi h'(t) dif x^i$; this is a global smooth 1-form on $M$.
  On the neighborhood where $chi = 1$, comparing the $dif x^i$
  components gives
  $h'(t) = (partial omega)/(partial x^i)(t, x')
  sum_(j=0)^infinity a_j omega(t, x')^j$.
  Since
  $(dif)/(dif t) omega(t, x')^(j+1)
  = (j+1) omega(t, x')^j (partial omega)/(partial x^i)(t, x')$,
  integrating in $t$ near $t_0$ gives
  $h(t) = C + sum_(j=0)^infinity a_j/(j+1) omega(t, x')^(j+1)$
  for some constant $C in RR$.
  Setting $b_0 = C$ and $b_(j+1) = a_j/(j+1)$ for $j >= 0$, we get
  $h(t) = sum_(j=0)^infinity b_j omega(t, x')^j$
  near $t_0$.
  Thus, with $psi(t) = omega(t, x')$ defined on a neighborhood
  of $t_0$, every $h in C^infinity (RR)$ is a power series in $psi$
  near $t_0$, which contradicts the lemma above.
]
