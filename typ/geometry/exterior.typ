#import "../shared.typ": *
#import "@preview/noteworthy:0.4.0": *

#show: tylenotes

= The Start

This note starts with the exterior derivative in Euclidean space,
which is the following.

#example[
  Derive the 2-form of the external differential by defining it in Euclidean space.
]

#solution[
  Let $omega = P d x + Q d y + R d z$,
  we deduce that
  $ d P = partial P_x d x + partial P_y d y + partial P_z d z $
  $ d Q = partial Q_x d x + partial Q_y d y + partial Q_z d z $
  $ d R = partial R_x d x + partial R_y d y + partial R_z d z $
  $ d omega = d P and d x + d Q and d y + d R and d z $.
  Expand item by item to obtain
  $ d P and d x = partial P_y d y and d x + partial P_z d z and d x $
  $ d Q and d y = partial Q_x d x and d y + partial Q_z d z and d y $
  $ d R and d z = partial R_x d x and d z + partial R_y d y and d z $.
  Substitute them into the expression of $d omega$, we obtain that
  $ d omega = 
  (partial R_y - partial Q_z) d y and d z +  
  (partial P_z - partial R_x) d z and d x +
  (partial Q_x - partial P_y) d x and d y $.
  And we are done.
]

= The Climax

But this solution is extremely ugly.
We obtain that $omega = mat(P, Q, R) vec(d x, d y, d z) $.
So is there a way to solve the problem through linear algebra?
Let's have a try.

#solution[
  We obtain that for any function $f$,
  $d f = mat(partial f_x, partial f_y, partial f_z) vec(d x, d y, d z)$.
  Let $omega = mat(P, Q, R) vec(d x, d y, d z)$,
  then $d omega = mat(d P, d Q, d R) vec(d x, d y, d z)$.

  Obtain that $mat(d P, d Q, d R) = mat(d x, d y, d z)
  mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  )$.
  Substitute this in, thus,
  $d omega = mat(d x, d y, d z) mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  ) vec(d x, d y, d z)$.

  Let $arrow(v) = vec(d x, d y, d z)$, $bold(A) = mat(
    partial P_x, partial P_y, partial P_z;
    partial Q_x, partial Q_y, partial Q_z;
    partial R_x, partial R_y, partial R_z;
  )$, then $d omega = arrow(v)^T bold(A) arrow(v)$.

  Here, we may need the following lemma.

  #lemma[
    Let $R$ be an exchange ring, $A$ is combination algebra on $R$.
    Let $arrow(v) in A^n$, for any matrix $bold(S) = (s_(i j)) in M_n (R)$,
    If $Q = arrow(v)^T bold(S) arrow(v)$, then
    $Q = sum^n_(i=1) sum^n_(j=1) s_(i j) v_i v_j$.
  ]

  Since $forall d x, d y, d x and d x = 0, d x and d y = - d y and d x$,
  after applying *Lemma 2.1*, we obtain that:
  $ d omega = 
  (partial R_y - partial Q_z) d y and d z +  
  (partial P_z - partial R_x) d z and d x +
  (partial Q_x - partial P_y) d x and d y $.
  And we are done.
]

= The End

Now, the only work is to prove *Lemma 2.1*, and here it is.

#proof[
  What are you looking at? It's just some dumb, straightforward calculation — do it.
]



