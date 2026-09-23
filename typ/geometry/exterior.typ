#import "../shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes.with(
  title: "Exterior Derivatives via Linear Algebra",
  date: "2026-08-11",
  tags: ("geometry", "lean"),
  summary: "Deriving the exterior derivative of a 1-form as a 2-form in Euclidean space.",
)

= The Start

This note starts with the exterior derivative in Euclidean space,
which is the following.

#example[
  Derive the 2-form of the external differential by defining it in Euclidean space.
]

#solution[
  Let $omega = P dif x + Q dif y + R dif z$,
  we deduce that
  $ dif P = partial P_x dif x + partial P_y dif y + partial P_z dif z $
  $ dif Q = partial Q_x dif x + partial Q_y dif y + partial Q_z dif z $
  $ dif R = partial R_x dif x + partial R_y dif y + partial R_z dif z $
  $ dif omega = dif P and dif x + dif Q and dif y + dif R and dif z $.
  Expand item by item to obtain
  $ dif P and dif x = partial P_y dif y and dif x + partial P_z dif z and dif x $
  $ dif Q and dif y = partial Q_x dif x and dif y + partial Q_z dif z and dif y $
  $ dif R and dif z = partial R_x dif x and dif z + partial R_y dif y and dif z $.
  Substitute them into the expression of $dif omega$, we obtain that
  $ dif omega = 
  (partial R_y - partial Q_z) dif y and dif z +  
  (partial P_z - partial R_x) dif z and dif x +
  (partial Q_x - partial P_y) dif x and dif y $.
  And we are done.
]

= The Climax

But this solution is extremely ugly.
We obtain that $omega = mat(P, Q, R) vec(dif x, dif y, dif z) $.
So is there a way to solve the problem through linear algebra?
Let's have a try.

#solution[
  We obtain that for any function $f$,
  $dif f = mat(partial f_x, partial f_y, partial f_z) vec(dif x, dif y, dif z)$.
  Let $omega = mat(P, Q, R) vec(dif x, dif y, dif z)$,
  then $dif omega = mat(dif P, dif Q, dif R) vec(dif x, dif y, dif z)$.

  Obtain that $mat(dif P, dif Q, dif R) = mat(dif x, dif y, dif z)
  mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  )$.
  Substitute this in, thus,
  $dif omega = mat(dif x, dif y, dif z) mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  ) vec(dif x, dif y, dif z)$.

  Let $arrow(v) = vec(dif x, dif y, dif z)$, $bold(A) = mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  )$, then $dif omega = arrow(v)^"T" bold(A) arrow(v)$.

  Here, we may need the following lemma.

  #lemma[
    Let $R$ be an exchange ring, $A$ is combination algebra on $R$.
    Let $arrow(v) in A^n$, for any matrix $bold(S) = (s_(i j)) in M_n (R)$,
    If $Q = arrow(v)^"T" bold(S) arrow(v)$, then
    $Q = sum^n_(i=1) sum^n_(j=1) s_(i j) v_i v_j$.
  ]

  Since $forall dif x, dif y, dif x and dif x = 0, dif x and dif y = - dif y and dif x$,
  after applying *Lemma 2.1*, we obtain that:
  $ dif omega = 
  (partial R_y - partial Q_z) dif y and dif z +  
  (partial P_z - partial R_x) dif z and dif x +
  (partial Q_x - partial P_y) dif x and dif y $.
  And we are done.
]

= The End

Now, the only work is to prove *Lemma 2.1*, and here it is.

#proof[
  What are you looking at? It's just some dumb, straightforward calculation — do it.
]



