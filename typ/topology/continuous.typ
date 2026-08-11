#import "../shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes

#theorem(title: "continuity")[
  Let $A subset RR$,
  a function $f:A -> RR$ is continuous if and only if
  $ forall "open set" U subset RR, exists "some open set" V subset RR, "such that" f^(-1)(U)=V inter A$.
]

#proof[
  Let $x_0 in A$, $epsilon > 0$.
  Setting $U subset RR = (f(x_0)-epsilon, f(x_0)+epsilon)$ and $f^(-1)(U) = V inter A$,
  where $V subset RR$.
  Then $x_0 in V$.
  Since $V$ is an open set, there exists $(x_0-delta, x_0+delta) subset V$.
  Because $x_0 in V inter A$, $V inter A$ is non-empty. 
  Hence, $forall x in RR "which makes" |x - x_0| < delta, |f(x)-f(x_0)|<epsilon$.
  Thus, $forall epsilon > 0, exists delta > 0, |x - x_0| < delta => |f(x)-f(x_0)| < epsilon$. \
  The converse is similar and is left to the reader.
]

