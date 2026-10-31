#import "@preview/noteworthy:0.4.0": noteworthy
#import "../shared.typ": *

#show: tylenotes.with(
  title: "IMO 1992 P2",
  date: "2026-10-31",
  tags: ("imo", "lean"),
  summary: "A solution for IMO 1992 P2",
)

#problem[
  Determine all functions $f: RR->RR$ such that
  $f(x^2+f(y))=y+f(x)^2$.
]

#note[
  We denote $f^2(x) = f(f(x))$.
]

#solution[
  Let $x = 0$, then $f^2(y)=y+f(0)^2$.
  Hence, $f^2$ is bijective,
  which implies $f$ is bijective.
  Hence, take $t in RR$ such that $f(t) = 0$.
  Let $a = f^2(t) = f(0)$.
  Let $x = t$, $y = 0$,
  then $f(t^2+a) = f(t)^2 = 0 = f(t)$.
  By bijectivity, we obtain $t^2 + a = t$.
  Let $x = 0$, $y = t$,
  it follows that
  $a = f^2(t) = t + f(0)^2 = t + a^2$.
  Substitute $t = t^2 + a$ in to obtain $t^2 + a^2 = 0$.
  Since $t^2 >= 0$ and $a^2 >= 0$, it follows that $t = 0$.
  Thus, $f(0) = 0$.
  Let $y = 0$ to obtain $f(x^2)=f(x)^2$.
  Let $a = x^2, b = f(y)$, then $a in [0,+infinity), b in RR$,
  and $f(a+b) = y + f(x)^2 = f(x^2) + f(f(y)) = f(a) + f(b)$.
  Then f is odd.
  Hence, $f(x+y)=f(x)+f(y) thick forall x,y in RR$.
  Since $f(x^2)=f(x)^2 >= 0$, $f(x)$ is monotone,
  then $f(x) = k x$.
  Substitute this in to obtain
  $k x^2 + k^2 y = y + k^2 x^2$,
  then $k^2-k=0$ and $k^2 = 1$.
  Thus, $k = 1$, which implies $f(x) = x$.
]

