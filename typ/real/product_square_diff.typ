#import "/typ/shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Infinite Product of Sums of Squares",
  date: "2026-09-18",
  tags: ("real", "lean"),
  summary: "Here we discuss how quickly the infinite product of sums of squares increases.",
)

= The Start

The story begins with the expression $x^2 - x^(-2)$, where $x > 0$.
By the difference of squares formula, we have
$ x^2 - x^(-2) = (x+x^(-1))(x-x^(-1)) = (x+x^(-1))(x^(1/2)+x^(-1/2))(x^(1/2)-x^(-1/2))=... $
Hence, let $a_i = x^(2^i) + x^(-2^i)$, then $a_i^2 = x^(2^(-(i-1)))+x^(-2^(-(i-1)))+2 = a_(i-1) + 2$,
which is $a_i = sqrt(a_(i-1)+2)$. Let $f(n) := a_0 dot a_1 dot a_2 dot ... dot a_n$,
$g(n) := x^(2^(-n)) - x^(-2^(-n))$, then $f(n) dot g(n) = x^2 + x^(-2)$,
which immediately gives that $f$ converges.
Now the problem is to find how fast $f$ increases and $g$ decreases.
It is obvious that we would require some approximations here.

= The Climax

First let $t = x^2 + x^(-2)$. Thus, $f(n) dot g(n) = t$.
Since we are making approximations for $f$ and $g$,
it is a good idea to apply $partial_n$ to both sides.
Hence, we obtain $f'(n)g(n) + f(n)g'(n)=0$,
which is $f'(n) = - (tg'(n))/(g(n)^2)$.

Without loss of generality, set $t = 1$ and $x = e$.
Thus, $g(n) = e^(2^(-n)) - e^(-2^(-n))$, $f'(n) = - (g'(n))/(g(n)^2)$.
Let $m = 2^n$, $hat(g)(m) = e^(1/m) - e^(-1/m)$.
Then $hat(f)(m) = - (hat(g)'(m))/(hat(g)(m)^2) = ((1/(m^2))e^(1/m) + 1/(m^2)e^(-1/m))/((e^(1/m)-e^(-1/m))^2)$.
Now, it is clear how to best estimate how fast $f$ increases and $g$ decreases.

= The End

The final result is here.

#theorem[
  $f(n)$ increases and $g(n)$ decreases like exponentials.
]

#proof[
 From the previous resut, we have
 $hat(f)(m) = ((1/(m^2))e^(1/m) + 1/(m^2)e^(-1/m))/((e^(1/m)-e^(-1/m))^2)$. 
 When $m$ is large enough, $e^(1/m) approx 1/m + 1$, $e^(-1/m) approx -1/m+1$.
 $therefore hat(f)'(m) approx (2/(m^2))/((2/m)^2)=1/2$.
 and $hat(g)'(m)=-1/(m^2)e^(1/m)-1/(m^2)e^(-1/m) approx -2/(m^2)$.
 $therefore hat(f)(m)=1/2 m$ and $hat(g)(m)=2/m$.
 Hence, $f(n)=2^(n-1)$ and $g(n)=2^(1-n)$.
]

