#import "/typ/shared.typ": *
#import "/phys/shared.typ": *
#import "@preview/noteworthy:0.4.0": *
#import "@preview/cetz:0.5.2": canvas, draw

#show: equations

#show: tylenotes.with(
  title: "Velocity in Horizontal Projection with Resistance",
  date: "2026-09-25",
  tags: ("kinematics", "projection"),
  summary: "Relationship between horizontal velocity and vertical velocity in horizontal projection with resistance.",
)

Horizontal projection is obviously easy, and thus very boring.
But if we consider linear resistance, things are different.

#canvas({
  import draw: *

  let x_max = 6.5
  let y_max = 6.0

  line((0, 0), (x_max, 0), stroke: black + 1pt, mark: (end: ">"))
  line((0, 0), (0, -y_max), stroke: black + 1pt, mark: (end: ">"))

  content((x_max + 0.2, 0), [x], anchor: "west")
  content((0, -y_max - 0.2), [y], anchor: "north")

  let v0x = 10.0
  let tau = 0.6
  let g = 9.8
  let v_ter = g * tau

  let t_max = 1.5
  let n = 30

  let pts = ()
  for i in range(n + 1) {
    let t = t_max * i / n
    let x = v0x * tau * (1 - calc.exp(-t / tau))
    let y = -(v_ter * t - v_ter * tau * (1 - calc.exp(-t / tau)))
    pts.push((x, y))
  }
  line(..pts, stroke: blue + 1.5pt)

  let t_p = 0.8
  let x_p = v0x * tau * (1 - calc.exp(-t_p / tau))
  let y_p = -(v_ter * t_p - v_ter * tau * (1 - calc.exp(-t_p / tau)))
  let vx_p = v0x * calc.exp(-t_p / tau)
  let vy_p = -v_ter * (1 - calc.exp(-t_p / tau))

  circle((x_p, y_p), radius: 0.08, fill: black, stroke: none)
  content((x_p + 0.15, y_p - 0.15), text(size: 10pt, $P$), anchor: "north-west")

  let v_scale = 0.35

  line((x_p, y_p), (x_p + vx_p * v_scale, y_p), stroke: red + 1pt, mark: (end: ">"))
  content((x_p + vx_p * v_scale / 2, y_p + 0.15), text(size: 8pt, fill: red, $v_x$), anchor: "south")

  line((x_p, y_p), (x_p, y_p + vy_p * v_scale), stroke: green + 1pt, mark: (end: ">"))
  content((x_p - 0.2, y_p + vy_p * v_scale / 2), text(size: 8pt, fill: green, $v_y$), anchor: "east")

  let v_end = (x_p + vx_p * v_scale, y_p + vy_p * v_scale)
  line((x_p, y_p), v_end, stroke: purple + 1.5pt, mark: (end: ">"))
  content((v_end.at(0) + 0.15, v_end.at(1) - 0.15), text(size: 8pt, fill: purple, $v$), anchor: "south-west")

  line((x_p, 0), (x_p, y_p), stroke: (paint: gray, thickness: 0.8pt, dash: "dashed"))
  line((0, y_p), (x_p, y_p), stroke: (paint: gray, thickness: 0.8pt, dash: "dashed"))

  content((0, 0), text(size: 9pt)[O], anchor: "north-east")
})

As shown in the figure, we discuss about the relationship between $v_x$ and $v_y$.
You can study it by solving ODEs, but we are not going to do that here, because it is boring.
However, I will show this solution here, in order to inpire you about what is going on here.

#solution[
  #set math.equation(numbering: none)
  Consider a projectile launched horizontally with initial velocity $v_0$ and no initial vertical velocity. Let $x$ be horizontal and $y$ be vertical upward. Linear drag is taken as $F_d = -k v$, and let $lambda = k/m$. The component ODEs are
  $ d v_x / d t = -lambda v_x, quad d v_y / d t = -g - lambda v_y, $
  with initial conditions
  $ v_x(0)=v_0, quad v_y(0)=0. $

  For $v_x$,
  $ (d v_x)/v_x = -lambda d t, $
  so
  $ v_x(t)=v_0 e^(-lambda t). $

  For $v_y$,
  $ d v_y / d t + lambda v_y = -g. $
  Using the integrating factor $e^(lambda t)$,
  $ d/d t (e^(lambda t) v_y) = -g e^(lambda t). $
  Integration gives
  $ e^(lambda t) v_y = -g/lambda e^(lambda t)+C, $
  hence
  $ v_y(t) = -g/lambda + C e^(-lambda t). $
  The initial condition $v_y(0)=0$ gives $C=g/lambda$, so
  $ v_y(t) = -g/lambda (1-e^(-lambda t)) = g/lambda (e^(-lambda t)-1). $

  Eliminate $t$ using
  $ e^(-lambda t) = v_x/v_0. $
  Then
  $ v_y = -g/lambda (1-v_x/v_0). $
  Equivalently,
  $ v_y = g/lambda (v_x/v_0 - 1), $
  or
  $ v_y + g/lambda = g/(lambda v_0) v_x. $

  Thus the velocity components satisfy the linear relation
  $ v_y = g/(lambda v_0) v_x - g/lambda. $
  The point $(v_x,v_y)$ lies on the straight line from $(v_0,0)$ to $(0,-g/lambda)$.
]

You can see that we got exponentials during the process,
but no exponential appeared in the final expression.
So maybe solving these equations isn't necessary here.
And indeed you do not need to solve them. Here is what I discovered.

#solution[
  It follows that
  $ a_x = - k/m v_x, $ <eq:x>
  $ a_y = - k/m v_y - g. $ <eq:y>
  Let the standard motion be
  $ a = -k/m v, $
  whose initial values are $a_0 = 0$, $v_0 = 1$.
  Then in kinematics sense $a$ and $v$ are uniquely determined.
  From @eq:x we have
  $ v_x = v_0 dot v. $ <eq:x_>
  From @eq:y we have 
  $ v_y + v_t = v_t dot v, $ <eq:y_>
  where $v_t = (m g)/k$.
  
  Hence, we obtain
  $ v_x / v_0 = v_y / v_t + 1. $
  Thus, $ (m g)/(k v_0) v_x = v_y + (m g)/k.  $
]

This is very simple and elegant.
However, there is another approach. It is not so simple, but it is more fundamental.

#solution[
  #set math.equation(numbering: none)

  Let the velocity space be $(v_x, v_y)$,
  then the velocity vector starts at $(v_0, 0)$.
  The terminal velocity is $V = (0, -(m g)/k)$.
  Then the residual velocity is $ u = v - V = (v_x, v_y + (m g)/k) $.
  Hence, $ a_u = - k/m u $.
  Since $a_u$ is always on the oppsite direction of $u$,
  we know that the endpoint of $u$ is a line over time in the velocity space.
  The initial value of this line is $u_0 = (v_0, (m g)/k)$, the end is $u = (0, 0)$.
  Thus, $ u(t) = (t, (m g)/(k v_0) t). $ Hence, $u_y = (m g)/(k v_0) u_x$.
  Since $u = (v_x, v_y+(m g)/k)$, we have
  $ (m g)/(k v_0) v_x = v_y + (m g)/k.  $
]

The reader can verify that the methods we use here can be extended to many other problems.

