#import "/typ/shared.typ": *
#import "/phys/shared.typ": *
#import "@preview/noteworthy:0.4.0": *
#import "@preview/cetz:0.5.2"

#show: tylenotes.with(
  title: "The Frequency of the Sling",
  date: "2026-09-24",
  tags: ("dynamics",),
  summary: "Analyze the sling by projection on the y-axis.",
)

= The Start

This is a sling.

#align(center)[
  #cetz.canvas({
    import cetz.draw: *

    let r = 0.4
    let d = 2
    let alpha = 1/2
    let beta = 1/3

    let y1 = d * alpha
    let y2 = d * beta

    let b1 = ball((-d, -y1), r: r)
    b1.draw

    let b2 = ball((0, 0), r: r)
    b2.draw
    content((0, 0), $A$)

    let b3 = ball((d, y2), r: r)
    b3.draw
    content((d, y2), $B$)

    connect(b1, b2, kind: "rod")
    connect(b2, b3, kind: "rod")
    
    let u = (b1.pos.at(0) - b2.pos.at(0), b1.pos.at(1) - b2.pos.at(1))
    let n = calc.sqrt(u.at(0) * u.at(0) + u.at(1) * u.at(1))
    let uh = (u.at(0) / n, u.at(1) / n)

    let perp = (-uh.at(1), uh.at(0))
    let perp = if perp.at(1) < 0 {
      (uh.at(1), -uh.at(0))
    } else {
      perp
    }

    let f = 1
    let origin = (
      b2.pos.at(0) + perp.at(0) * r,
      b2.pos.at(1) + perp.at(1) * r,
    )
    let tip = (
      origin.at(0) + perp.at(0) * f,
      origin.at(1) + perp.at(1) * f,
    )

    vector(origin, tip)
    content(tip, $F$, anchor: "south")  })
]
By experiment, I obtained that when the frequency of A and B differs from each other too much,
B will soon stop moving.

#solution[
  It is clearly a stupid idea to directly solve the ODEs of this system,
  since there is no analytic solution to them.
  Hence, let's project the system onto the y-axis.
  Using A as the reference frame,
  we obtain that the motion of B in the vertical direction is approximately forced oscillation.
  Hence, we represent B's motion as the form below,

  #align(center)[
    #cetz.canvas({
      import cetz.draw: *

      let r = 0.4
      vector((0, r), (0, 1.2))
      content((r, 0.7), $F$)
      ball((0, 0), r: r).draw
      content((0, 0), $B$)
      spring((0, -r), (0, -2))
      ground((-2, -2), (2, -2), side: -1)
    })
  ]

  where $F = F_0 cos Omega t$, $Omega$ is the angular frequency associated with the frequency of $F$,
  and $a_0 = F_0/m$ is the acceleration amplitude.
  It follows that $ m (dif^2 y)/(dif t^2) = - k y - m g - F_0 cos Omega t. $
  The solution of this ODE is $y = (g/(omega^2) - a_0/(Omega^2 - omega^2)) cos omega t - g/(omega^2) + (a_0/(Omega^2 - omega^2)) cos Omega t$,
  where $sqrt(k/m) = omega$.
  Thus, we obtain $ y = (g/(omega^2) - a_0/(Omega^2 - omega^2)) cos omega t - g/(omega^2) + (a_0/(Omega^2 - omega^2)) cos Omega t. $

  When $|omega - Omega| >> 0$, $a_0/Omega^2 >> g/(omega^2)$.
  Hence, $
    y approx (a_0/Omega^2)(cos Omega t - cos omega t) - g/(omega^2)
    = - 2 (a_0/Omega^2) sin((omega + Omega)/2 t) sin((Omega - omega)/2 t) - g/(omega^2).
  $
  $omega$ is a constant and $omega << Omega$ usually holds.
  Therefore, we obtain $
    y approx - 2 (a_0/Omega^2) sin^2(Omega/2 t) - g/(omega^2) = (a_0/Omega^2) cos(Omega t) - a_0/Omega^2 - g/(omega^2).
  $
  Switch to the reference frame of the ground, we obtain
  $ y' = y + (-(a_0/Omega^2) cos(Omega t)) = - a_0/Omega^2 - g/(omega^2), $
  this gives no oscillation, which is exactly what experiments give us.
]

#note[
  When $omega = Omega$, 
  it follows that $ y = g/(omega^2)(cos(omega t) - 1), $
  Still, by switching to the reference frame of the ground,
  we obtain $ y' = y+(-(a_0/Omega^2) cos(Omega t)) = g/(omega^2)(cos(omega t) - 1) - (a_0/Omega^2) cos(Omega t). $
  Since $omega = Omega$, $a_0 -> 0$, it follows that
  $ y' = g/(omega^2)(cos(omega t) - 1), $
  which is a common oscillation.
]

