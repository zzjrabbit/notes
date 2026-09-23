#import "/typ/shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Yet Another Definition of Euler's Number",
  date: "2026-09-18",
  tags: ("real", "lean"),
  summary: "Provide a new way of defining e from the tangent-line inequality.",
)

= The Start

This note begin with the question:
can we use the properties of $ln$ to obtain the tangent-line inequality algebraically?
(Note that the tangent-line inequality means the inequality $ln(x) <= x - 1$.)
Here is what I tried.

First, let $I_n = (k 2^n,k 2^(n+1)]$, where $n in N$, $k in [1,2)$.
Hence we know that this can cover $(1,+infinity)$.
In fact, you can check that the same can be made for $(0,1)$, which is left to the reader.
We next show that if the inequality holds on $I_n$, then it holds on $I_(n+1)$,
which is basically an induction over intervals rather than integers.
Here, our inductive hypothesis is $ln(x) <= x - 1, forall x in I_n$.
Hence, we have $ln(2 x) = ln(2) + ln(x) <= ln(2) + x - 1, forall x in I_n$.
Since $I_n$ covers $(1,+infinity)$, $x > 1 > ln(2)$.
Thus, $ln(2 x) < x + x - 1 = 2 x - 1$. Since $x in I_n$, we obtain $2 x in I_(n+1)$.
Hence, $ln(x) < x - 1, forall x in I_(n+1)$.

The problem is the proof of the inequality on $I_0$, which is $(1,4)$.

But you will soon find it as difficult as the orignal case,
which I will explain later.

= The Climax

I thought at first that the following theorem and proof would help.

#theorem[
  $ ln(k) < k, forall k > 0 $
]

#proof[
  We first prove that $ln(k) < k, forall k > 0$.
  Since $e > 2$, you can verify that $ln(k) < log_2(k)$.
  Thus, it suffices to show that $log_2(k) < k$, which can be written as $k < 2^k$.
  We show it by induction.
  + $k in (0,1]$ Hence, $log_2(k) <= 0 < k$.
  + $log_2(k) < k$,also $k < 2^k and k > 1$ By $k>1$ we have $k+1 < 2 k < 2 dot 2^k = 2^(k+1)$.
  Hence, $ln k < k, forall k > 0$.
]

The problem is very obvious. Here the inequality still holds for $y=log_2(x)$.
But in our case, the inequality is false for any other logarithm.
The main problem is that this inequality depends on the property of $e$,
so that we cannot prove it unless we use the definition of $e$,
which makes the proof non-algebraic. Hence, our goal is impossible.
Yet there is another question. Since this inequality is deeply dependent on the definition of $e$,
is it possible to define $e$ with this inequality?
The answer is yes.

= The End
This theorem and the following proof gives you exactly how to define $e$ with our inequality.

#theorem[
  There exists a unique smooth function $f: R_+ -> R$ with the following property:
  + $f(x y) = f(x) + f(y)$ ($x,y>0$).
  + $f(x) <= x - 1$ ; equality holds if and only if $x=1$.
  We define $e$ to be a positive real number such that $f(e)=1$,
  and this definition is equivalent to the limit version.
]

#proof[
  We first show that $f$ is unique.
  Since $f(1) = f(1 dot 1) = 2 f(1)$, we obtain $f(1) = 0$.
  Apply $partial y$ to both sides of $f(x y) = f(x) + f(y)$, we have $x f'(x y) = f'(y)$.
  Let $y = 1$, we obtain $x f'(x) = f'(1)$.
  Hence, $f'(x) = C / x$, where $C = f'(1)$.
  Since $f(x) <= x - 1$, we let $g(x) := f(x) - (x-1)$.
  Because the equality holds if and only if $x = 1$,
  we know that $g$ has the maximum value at $1$, Hence $g'(1) = 0$.
  It follows that $g'(x) = f'(x) - 1$.
  Substitute this into the previous expression to obtain
  $f'(1) = 1$. Hence, $f'(x) = 1/x$.
  Thus, we obtain $ f(x) = integral_1^x 1/x dif x. $
  Hence, $f$ is unique.

  We next show that our definition of $e$ is equivalent to the limit version.
  Let $F(x) := f(x y) - f(x) - f(y)$, where $y$ is a constant.
  Since $F'(x) = 1/x - 1/x = 0$, $F(x)$ is a constant.
  Because $F(1) = f(y) - f(1) - f(y) = 0$, we have $F(x) = 0$.
  Thus, we obtain $ f(x y) = f(x) + f(y). $
  Since $f$ is defined upon $R_+$, $f'(x) = 1/x > 0$. Hence $f$ is injective.
  Let $exp$ be the inverse function of $f$.
  By the inverse function theorem, $exp'(x) = exp(x)$.
  By $f(x y) = f(x) + f(y)$, we have $exp(x+y) = exp(x)exp(y)$.
  Since $f$ is smooth, we know that $exp$ is smooth.
  By continuity, we can denote $exp$ as $e^x$, where $e = exp(1)$(equivalent to $f(e) = 1$).
  From $f(x) <= x - 1$, we know that $e^x >= x + 1$,
  which implies $e^(1/n) >= 1/n + 1$, which is
  $ e >= (1 + 1/n)^n. $
  Also, $e^(-1/(n+1)) >= 1 - 1/(n+1)$, which is
  $ e^(-1/(n+1)) >= n/(n+1). $
  Thus, $e^(1/(n+1)) <= 1 + 1/n$.
  Hence, we obtain $ (1 + 1/n)^n <= e <= (1 + 1/n)^(n + 1), forall n in N $
  Since $f$ and $exp$ are well-defined, $e$ exists uniquely.
  Hence, $lim_(n->infinity)(1+1/n)^n$ and $lim_(n->infinity)(1+1/n)^(n+1)$ converges.
  Because $(lim_(n->infinity)(1+1/n)^(n+1)) / (lim_(n->infinity)(1+1/n)^n)$ = 
  $lim_(n->infinity)(1+1/n) = 1$ implies
  $lim_(n->infinity)(1+1/n)^n = lim_(n->infinity)(1+1/n)^(n+1)$.
  By the squeeze theorem, we obtain $ e=lim_(n->infinity)(1+1/n)^n. $

]

