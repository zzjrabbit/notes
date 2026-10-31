#import "@preview/noteworthy:0.4.0": noteworthy
#import "../shared.typ": *

#show: tylenotes.with(
  title: "Functional Equations with Finitely Many Ratios",
  date: "2026-10-30",
  tags: ("functional equation", "finite sets", "lean"),
  summary: "A technique for solving a functional equation with finitely many ratios",
)

#problem[
  Determine all functions $f: RR->RR$ such that
  + $f(x+y) + f(x-y) = 2f(x) + 2f(y)$
  + $f(x y) = f(x) f(y)$
  + $f(1) = 1$
  + $forall x in RR, exists n in {1,2,dots,10}$ such that $f(x) = n x^2$.
]

#solution[
  It's not hard to see that the final answer is $f(x) = x^2$.
  Next we prove it. \
  Let $x = 0$, $y = 0$, then $2f(0) = 4f(0)$. Hence, $f(0) = 0$.
  Let $x = 0$, we obtain $f(y) + f(-y) = 2f(y)$.
  Thus, $f(y) = f(-y)$. Therefore $f(-1) = 1$. \
  Then we will show that $f(n) = n^2 thick forall n in ZZ$.
  By $f(y) = f(-y)$,
  it suffices to show that $f(n) = n^2 thick forall n in NN$.
  Since $f(0) = 0$ and $f(1)=1^2$ are already known,
  by induction, we obtain
  $f(n) = f(n-1 + 1) = -f(n-2) + 2f(n-1) + 2f(1)
  = -(n-2)^2 + 2(n-1)^2 + 2 = n^2$. \
  Next, suppose $f(x) = phi(x)x^2$.
  We stipulate that $phi(0) = 1$, since $f(0) = 0$.
  Then we obtain $phi: RR->{1,2,dots,10}$.
  We study the case in which $x eq.not 0$,
  since we already know that $f(0) = 0$.
  By property 1, we obtain 
  $phi(x+y)(x+y)^2 + phi(x-y)(x-y)^2 = 2phi(x)x^2 + 2phi(y)y^2$.
  Simplify this expression to obtain
  $(phi(x+y)+phi(x-y)-2phi(x))x^2+(phi(x+y)+phi(x-y)-2phi(y))y^2+
  2(phi(x+y)-phi(x-y))x y = 0$.
  Then we will show that
  $exists y in ZZ$ such that $phi(x)=phi(y)$.
  Let $a = phi(x+y)+phi(x-y)-2phi(x)$,
  $b = phi(x+y)+phi(x-y)-2phi(y)$,
  $c = 2phi(x+y)-2phi(x-y)$,
  then $a x^2 + b y^2 + c x y = 0$.
  Since $phi$ is a bounded integer-valued function,
  we know that there are only finitely
  many possibilities of $(a,b,c)$.
  Thus, this equation gives at most finitely many solutions
  of $y$ satisfying this condition for a given $x$ when 
  $a$, $b$, $c$ is not all zero.
  But $y in ZZ$ can take infinitely many values.
  Thus, $exists y$ such that $a=b=c=0$ for a given $x$.
  In this case,
  we obtain $phi(x+y)+phi(x-y)=2phi(x)=2phi(y)$,
  which implies $phi(x)=phi(y)$.

  Last, since $forall x in RR, exists y in ZZ, phi(x)=phi(y)$
  and $phi(x)=1 thick forall x in ZZ$,
  we obtain $phi(x)=1 thick forall x in RR$.
  Thus, $f(x)=x^2$.
]

