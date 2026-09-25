#import "/typ/shared.typ": *
#import "/phys/shared.typ": *
#import "@preview/noteworthy:0.4.0": *
#import "@preview/cetz:0.5.2"

#show: equations

#show: tylenotes.with(
  title: "Derivation of the Catenary Equation",
  date: "2026-09-24",
  tags: ("statics",),
  summary: "Derive the form of the catenary using the infinitesimal method.",
)

This, is a catenary.

#let catenary(
  a, b,
  sag: 0.15,
  side: -1,
  samples: 40,
  ..s,
) = {
  if sag == 0 {
    draw.line(a, b, ..s)
  } else {
    let (x1, y1) = (a.at(0), a.at(1))
    let (x2, y2) = (b.at(0), b.at(1))
    let dx = x2 - x1
    let dy = y2 - y1
    let len = calc.sqrt(dx * dx + dy * dy)
    // Unit normal to the chord, flipped by `side`.
    let nx = -dy / len * side
    let ny = dx / len * side
    let pts = ()
    for i in range(samples + 1) {
      let t = i / samples
      let dip = 4 * t * (1 - t) * sag
      pts.push((
        x1 + dx * t + nx * dip,
        y1 + dy * t + ny * dip,
      ))
    }
    draw.line(..pts, ..s)
  }
}

#cetz.canvas({
  import cetz.draw: *

  ground((-4, 0), (4, 0))
  catenary((-3, 0), (3, 0), sag: 1.0)
})

It is not so obvious that this is not a parabola.
But I will expalin here.
Suppose that there is a ball being thrown out(note that we are not considering resistance here).
Since there is no resistance, we know that its velocity on the horizontal direction is a constant.
Therefore, if we make its path, which is a parabola, a rope, then its mass is uniform on the vertical direction.
The problem is, in the case of catenary, the mass is uniform over the rope itself, not over the vertical direction.
Thus, a catenary is not a parabola.

But what is it? Here is a solution.

#solution[
  #let _pt(a, b, sag, t) = {
    let (x1, y1) = (a.at(0), a.at(1))
    let (x2, y2) = (b.at(0), b.at(1))
    let dx = x2 - x1
    let dy = y2 - y1
    let L = calc.sqrt(dx * dx + dy * dy)
    let nx = dy / L
    let ny = -dx / L
    let d = 4 * t * (1 - t) * sag
    (x1 + dx * t + nx * d, y1 + dy * t + ny * d)
  }

  #let _tan(a, b, sag, t) = {
    let h = 1e-4
    let p1 = _pt(a, b, sag, t - h)
    let p2 = _pt(a, b, sag, t + h)
    let dx = p2.at(0) - p1.at(0)
    let dy = p2.at(1) - p1.at(1)
    let n = calc.sqrt(dx * dx + dy * dy)
    (dx / n, dy / n)
  }

  #cetz.canvas({
    import cetz.draw: *

    let a = (-7, 0)
    let b = (7, 0)
    let sag = 3.5
    let half = 0.5
    let t0 = 0.24
    let t1 = 0.33

    // Ceiling
    line((-9.5, 0), (-1.5, 0), stroke: (thickness: 1.8pt))
    for i in range(33) {
      let x = -9.5 + i * 0.25
      line((x, 0), (x + 0.15, 0.18), stroke: (thickness: 0.6pt))
    }

    // Left half of the rope, gray
    let pts = ()
    for i in range(81) {
      pts.push(_pt(a, b, sag, half * i / 80))
    }
    line(..pts, stroke: (thickness: 1.2pt, paint: rgb("#999")))

    // Highlighted element, thick black
    let epts = ()
    for i in range(31) {
      epts.push(_pt(a, b, sag, t0 + (t1 - t0) * i / 30))
    }
    line(..epts, stroke: (thickness: 3.0pt))

    let p0 = _pt(a, b, sag, t0)
    let p1 = _pt(a, b, sag, t1)
    let tan0 = _tan(a, b, sag, t0)
    let tan1 = _tan(a, b, sag, t1)

    // F at the left end of the element
    let Lf = 1.3
    let tip0 = (p0.at(0) - tan0.at(0) * Lf, p0.at(1) - tan0.at(1) * Lf)
    line(p0, tip0, mark: (end: ">"), stroke: (thickness: 1.2pt))
    content(tip0, $F$, anchor: "north-east")

    // F' at the right end
    let tip1 = (p1.at(0) + tan1.at(0) * Lf, p1.at(1) + tan1.at(1) * Lf)
    line(p1, tip1, mark: (end: ">"), stroke: (thickness: 1.2pt))
    content(tip1, $F'$, anchor: "north-west")

    // Vertical dashed projections from the element endpoints up to the ceiling
    line(
      p0,
      (p0.at(0), 0),
      stroke: (dash: "dashed", thickness: 0.6pt, paint: rgb("#666")),
    )
    line(
      p1,
      (p1.at(0), 0),
      stroke: (dash: "dashed", thickness: 0.6pt, paint: rgb("#666")),
    )

    // dx label between the two projection lines, just below the ceiling
    let x0 = p0.at(0)
    let x1 = p1.at(0)
    content(((x0 + x1) / 2, -0.12), $dif x$, anchor: "north")

    // F_0 at a, forward along the tangent
    let tan_start = _tan(a, b, sag, 0)
    let F0_len = 2.2
    let F0_tip = (
      a.at(0) + tan_start.at(0) * F0_len,
      a.at(1) + tan_start.at(1) * F0_len,
    )
    line(a, F0_tip, mark: (end: ">"), stroke: (thickness: 1.6pt, paint: red))
    content(F0_tip, $F_0$, anchor: "north-east")

    line(
      a,
      (a.at(0) + 2.6, a.at(1)),
      stroke: (dash: "dashed", thickness: 0.6pt, paint: rgb("#666")),
    )

    let ang1 = calc.atan2(tan_start.at(0), tan_start.at(1)) / 1rad
    let r_arc = 1.2
    let n_arc = 24
    let arc_pts = ()
    for i in range(n_arc + 1) {
      let ang = (ang1 * i) / n_arc
      arc_pts.push((
        a.at(0) + r_arc * calc.cos(ang * 1rad),
        a.at(1) + r_arc * calc.sin(ang * 1rad),
      ))
    }
    line(..arc_pts, stroke: (thickness: 0.7pt, paint: rgb("#444")))

    let mid_ang = ang1 / 2
    content(
      (
        a.at(0) + 0.85 * calc.cos(mid_ang * 1rad),
        a.at(1) + 0.85 * calc.sin(mid_ang * 1rad),
      ),
      $theta_0$,
      anchor: "center",
    )
  })

  As shown in the figure, take a small segment of the heavy rope corresponding to $dif x$.
  its mass is $ dif m = lambda dif l = lambda (dif x) / cos(theta). $ <eq:m>
  Meanwhile, we obtain the following equations.
  $ F cos theta = F' cos(theta - dif theta) = (m g)/ (tan theta_0), $ <eq:fcos>
  $  F sin theta - F' sin(theta - dif theta) = dif m g, $ <eq:fsin>
  where
  $ cos(theta - dif theta) = 
    cos theta cos dif theta + sin theta sin dif theta approx
    cos theta + dif theta sin theta, $ <eq:app_cos>
  $ sin(theta - dif theta) = 
    sin theta cos dif theta - cos theta sin dif theta approx 
    sin theta - dif theta cos theta. $ <eq:app_sin>
  Substitute @eq:app_cos into @eq:fcos and @eq:app_sin into @eq:fsin to obtain
  $ F cos theta = F' cos theta + dif theta F' sin theta = (m g)/(tan theta_0) $ <eq:fcosa>
  $ F sin theta - F' sin theta + dif theta F' cos theta = dif m g $ <eq:fsina>
  By @eq:fcosa we have $F' cos theta = F cos theta - dif theta F' sin theta$.
  Multiply by $(sin theta) / (cos theta)$ on both sides to obtain
  $ F' sin theta = F sin theta - dif theta F' (sin^2 theta) / (cos theta). $ <eq:f_sin>
  Substitute @eq:f_sin into @eq:fsina, we obtain
  #math.equation(block: true, numbering: none, $ 
    F sin theta - F sin theta + dif theta F' (sin^2 theta)/(cos theta) + dif theta F' cos theta = dif m g,
  $ )
  which is $ d theta F' / ( cos theta ) = dif m g. $ <eq:no_f>
  Substitute @eq:m into @eq:no_f to obtain
  #[
    #set math.equation(numbering: none)
    $ dif theta F' / (cos theta) = (lambda dif x g) / (cos theta), $
    which is $ dif theta F' = lambda dif x g. $
    Hence, we obtain $ dif theta F' cos theta = lambda dif x g cos theta. $
  ]
  Since $F approx F'$, we have
  $ dif theta F cos theta = lambda dif x g cos theta. $ <eq:before_final>
  Substitute @eq:fcosa into @eq:before_final to obtain
  #math.equation(block: true, numbering: none,
    $ dif theta (m g)/(tan theta_0) = lambda dif x g cos theta, $
  )
  which is $ (dif theta)/(dif x) = lambda/m tan theta_0 cos theta. $
  Let $k = lambda/m tan theta_0$, we have
  $ (dif theta) / (dif x) = k cos theta. $ <eq:ode1>
  It is obvious that $ tan theta = (dif y)/(dif x). $ <eq:tan>
  By applying $dif/(dif x)$ to both sides of @eq:tan, we obtain that
  $ 1/(cos^2 theta) (dif theta)/(dif x) = (dif^2 y)/(dif x^2). $
  Substitute @eq:ode1 in, we have
  $ k/(cos theta) = (dif^2 y)/(dif x^2). $ <eq:ode2>
  Since $tan theta = (sin theta)/(cos theta) = sqrt(1/(cos^2 theta) - 1)$,
  we have $ cos theta = 1/sqrt(tan^2 theta + 1). $ <eq:cos>
  Substitute @eq:cos into @eq:ode2, we have
  $ k sqrt(tan^2 theta + 1) = (dif^2 y)/(dif x^2). $
  Substitute @eq:tan in, we obtain
  $ (dif^2 y)/(dif x^2) = k sqrt( ((dif y)/(dif x))^2 + 1 ). $ <eq:ode>
  Take $phi = (dif y)/(dif x)$, we have $ (dif phi)/(dif x) = k sqrt(phi^2 + 1). $
  The solution to this equation is $phi = sinh(k x)$.

  Hence, we obtain $ (dif y)/(dif x) = sinh(k x). $
  The solution is $y = 1/k cosh(k x) + C$.

  #set math.equation(numbering: none)

  Let the lowest point be $(0,0)$, we obtain
  $ y = 1/k cosh(k x) - 1/k. $

  Hence, the form of a catenary is $ y = 1/k cosh(k x) - 1/k, $
  where $k = lambda/m tan theta_0$.
]

Here, you can see that a catenary is the image of $cosh$,
which looks like a parabola, but not quite the same.

