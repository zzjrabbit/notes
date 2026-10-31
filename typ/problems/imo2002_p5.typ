#import "@preview/noteworthy:0.4.0": noteworthy
#import "../shared.typ": *

#show: tylenotes.with(
  title: "IMO 2002 P5",
  date: "2026-10-31",
  tags: ("imo", "lean"),
  summary: "Two solutions for IMO 2002 P5",
)

#problem[
  Determine all functions $f: RR->RR$ such that
  $(f(x)+f(y))(f(u)+f(v))=f(x u - y v) + f(x v + y u)$.
]

#solution[
  Let $x=y=u=v=0$ to obtain
  $4 f(0)^2 = 2 f(0)$,
  which implies $f(0) = 0$ or $1/2$.
  We consider the problem in two cases.
  + $f(0) = 0$. \
    Let $u = v = 1$ to obtain $2f(1)f(x)+2f(1)f(y)=f(x-y)+f(x+y)$.
    Let $x = 0$, then $2f(1)f(y)=f(y) + f(-y)$.
    Hence, $(2f(1)-1)f(y) = f(-y)$.
    Let $x=1,u=1,y=v=0$ to obtain $f(1)^2=f(1)$.
    + $f(1) = 0$.
      Then $f(x+y)+f(x-y) = 0$.
      Let $x=y$ to obtain $f(2x)=0$. Hence, $f(x) eq.triple 0$.
    + $f(1) = 1$.
      There are two approaches.
      I state this case as a lemma and provide two proofs.
      See them below.
  + $f(0) = 1/2$. \
    Let $u=v=1$ to obtain $2f(1)f(x)+2f(1)f(y) = f(x-y)+f(x+y)$.
    Let $x = 0$, then $f(1)+2f(1)f(y) = f(-y)+f(y)$.
    When $y = 0$, it follows that
    $2f(1)=1$.
    Hence, $f(1)=1/2$.
    Thus, $f(y)+f(-y) = 1/2+f(y)$.
    Therefore $f(x) eq.triple 1/2$.
  Therefore, the final answers are
  $f(x) eq.triple 0$, $f(x) eq.triple 1/2$
  and $f(x) eq x^2$.
]

#lemma[
  Given function $f:RR->RR$ with
  + $(f(x)+f(y))(f(u)+f(v))=f(x u - y v) + f(x v + y u)$
  + $f(0) = 0$
  + $f(1) = 1$
  Prove that $f(x) = x^2$.
]

#proof[
  Take $u = v = 1, x = 0$ to obtain
  $2f(y) = f(y) + f(-y)$, which implies $f(y) = f(-y)$.
  Let $y = v = 0$, then $f(x)f(u)=f(x u)$.
  Hence, $f(x^2) = f(x)^2 >= 0$,
  which implies $x >= 0 => f(x) >= 0$.
  Let $u = x$, $v = -y$ to obtain
  $(f(x)+f(y))^2 = f(x^2+y^2)$.
  Let $phi(x) = f(sqrt(x)), x in [0, +infinity)$,
  then by multiplication,
  we have $phi(x) = sqrt(f(x)) >= 0$
  and $phi(x)phi(y) = phi(x y)$.
  Hence, $phi(x^2) + phi(y^2) = phi(x^2 + y^2)$.
  Since $phi(x) >= 0 thick forall x in [0,+infinity)$,
  we obtain $phi$ to be monotone on its domain.
  Hence, $forall x >= 0, phi(x) = k x$, where $k in RR$.
  Since $f(1) = 1$, it follows that $k = 1$.
  Thus, $forall x >= 0, phi(x) = x$.
  Therefore $forall x >= 0, f(x) = x^2$.
  By $f(y) = f(-y)$, we obtain $f(x) = x^2$.
]

#proof[
  Let $u = v = 1$,
  then $2f(x) + 2f(y) = f(x+y) + f(x-y)$.
  Let $x = 0$, it follows that $f(y) = f(-y)$.
  Take $y = 1$ to obtain
  $f(x+1) = 2f(x)+2-f(x-1)$.
  Since $f(0) = 0$, $f(1) = 1$,
  by induction,
  $f(n+1) = 2f(n)+2-f(n-1) = 2n^2+2-(n-1)^2=(n+1)^2$
  implies $f(n) = n^2 thick forall n in NN$.
  By $f(y) = f(-y)$, it follows that $f(n) = n^2 thick forall n in ZZ$.
  Let $y = v = 0$ to obtain $f(x)f(u)=f(x u)$,
  then it is not hard to show that
  $f(q) = q^2 thick forall q in QQ$.
  Since $f(x)f(u) = f(x u)$,
  $f(x^2) = f(x)^2 >= 0$,
  which implies $x>=0 => f(x) >= 0$.
  Let $x,y >= 0$, $u = x$, $v = -y$ to obtain
  $f(x^2+y^2) = (f(x)+f(y))^2 = f(x)^2 + 2f(x)f(y)+f(y)^2
  = f(x^2) + 2f(x)f(y)+f(y)^2 >= f(x^2)$.
  Hence, $f$ is monotone on $[0, +infinity)$.
  Hence, $forall x >= 0, f(x) = x^2$.
  By $f(x) = f(-x)$, it follows immediately that
  $f(x) = x^2$.
]

