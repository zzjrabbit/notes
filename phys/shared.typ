// shared.typ
// Physics drawing primitives for CeTZ 0.5.2.
//
// Visual convention:
// - rod: thick solid line with round caps, reads as a rigid bar.
// - rope: thin line with a slight sag, reads as a flexible string.
// - spring / wave / zigzag: CeTZ decorations.
//
// Each body returns a dict with `draw`, `pos`, `boundary`, and `name`.
// Emit `obj.draw` to render, feed `obj` into `connect` to link bodies.

#import "@preview/cetz:0.5.2": draw, decorations

// ---------- Low-level helpers ----------

#let _sub(a, b) = (a.at(0) - b.at(0), a.at(1) - b.at(1))
#let _add(a, b) = (a.at(0) + b.at(0), a.at(1) + b.at(1))
#let _scale(v, k) = (v.at(0) * k, v.at(1) * k)
#let _len(v) = calc.sqrt(v.at(0) * v.at(0) + v.at(1) * v.at(1))
#let _unit(v) = {
  let n = _len(v)
  if n == 0 { panic("_unit: zero vector") }
  (v.at(0) / n, v.at(1) / n)
}
#let _perp(v) = (-v.at(1), v.at(0))

// Default strokes per element kind. Users override by passing `stroke`.
#let _rod-stroke = (thickness: 2pt, paint: black, cap: "round")
#let _rope-stroke = (thickness: 0.7pt, paint: black)

// ---------- Connection ----------

// Attach two bodies with a visual link.
//
// - kind: "rod" | "rope" | "spring" | "wave" | "zigzag"
// - sag: rope only, downward bulge. Ignored for other kinds.
// - amplitude / segments: forwarded to CeTZ decorations.
#let connect(
  a, b,
  kind: "rod",
  sag: 0.15,
  amplitude: 0.25,
  segments: 10,
  name: none,
  ..s,
) = {
  let pa = a.pos
  let pb = b.pos
  let d = _sub(pb, pa)
  let dist = _len(d)
  if dist == 0 { panic("connect: centers coincide") }

  let u = _unit(d)
  let p1 = (a.boundary)(u)
  let p2 = (b.boundary)(_scale(u, -1))
  let user = s.named()

  if kind == "rod" {
    draw.line(p1, p2, name: name, ..(stroke: _rod-stroke) + user)
  } else if kind == "rope" {
    let style = (stroke: _rope-stroke) + user
    if sag == 0 {
      draw.line(p1, p2, name: name, ..style)
    } else {
      let mid = _add(_scale(_add(p1, p2), 0.5), _scale(_perp(u), sag))
      draw.bezier(p1, mid, p2, name: name, ..style)
    }
  } else {
    let path = draw.line(p1, p2, ..user)
    if kind == "spring" {
      decorations.coil(path, amplitude: amplitude, segments: segments, name: name)
    } else if kind == "wave" {
      decorations.wave(path, amplitude: amplitude, segments: segments, name: name)
    } else if kind == "zigzag" {
      decorations.zigzag(path, amplitude: amplitude, segments: segments, name: name)
    } else {
      panic("connect: unknown kind `" + kind + "`")
    }
  }
}

// ---------- Bodies ----------

#let ball(pos, r: 0.25, name: none, ..s) = (
  draw: draw.circle(pos, radius: r, name: name, ..s),
  pos: pos,
  r: r,
  name: name,
  boundary: dir => _add(pos, _scale(dir, r)),
)

#let block(center, w: 0.6, h: 0.4, name: none, ..s) = (
  draw: draw.rect(
    _sub(center, (w / 2, h / 2)),
    _add(center, (w / 2, h / 2)),
    name: name,
    ..s,
  ),
  pos: center,
  w: w,
  h: h,
  name: name,
  boundary: dir => {
    let ux = dir.at(0)
    let uy = dir.at(1)
    let tx = if ux == 0 { calc.inf } else { (w / 2) / calc.abs(ux) }
    let ty = if uy == 0 { calc.inf } else { (h / 2) / calc.abs(uy) }
    let t = calc.min(tx, ty)
    _add(center, _scale(dir, t))
  },
)

#let pulley(pos, r: 0.3, name: none, ..s) = (
  draw: draw.circle(pos, radius: r, name: name, ..s)
        + draw.circle(pos, radius: r * 0.12, fill: black),
  pos: pos,
  r: r,
  name: name,
  boundary: dir => _add(pos, _scale(dir, r)),
)

#let pivot(pos, size: 0.18, name: none, ..s) = (
  draw: draw.line(
    pos,
    _add(pos, (-size, -size * 1.5)),
    _add(pos, (size, -size * 1.5)),
    close: true,
    name: name,
    ..(fill: black) + s.named(),
  ),
  pos: pos,
  r: size,
  name: name,
  boundary: dir => pos,
)

#let hinge(pos, r: 0.06, name: none, ..s) = (
  draw: draw.circle(pos, radius: r, name: name, ..(fill: black) + s.named()),
  pos: pos,
  r: r,
  name: name,
  boundary: dir => pos,
)

// ---------- Auxiliary elements ----------

// Straight rigid bar. Defaults to a thick round-capped line.
#let rod(a, b, name: none, ..s) = {
  draw.line(a, b, name: name, ..(stroke: _rod-stroke) + s.named())
}

// Flexible rope. Defaults to a thin line with a slight sag.
// Pass `sag: 0` to draw it taut.
#let rope(a, b, sag: 0.15, name: none, ..s) = {
  let style = (stroke: _rope-stroke) + s.named()
  if sag == 0 {
    draw.line(a, b, name: name, ..style)
  } else {
    let d = _sub(b, a)
    let mid = _add(_scale(_add(a, b), 0.5), _scale(_perp(_unit(d)), sag))
    draw.bezier(a, mid, b, name: name, ..style)
  }
}

#let ground(
  a, b,
  hatch: 0.18, gap: 0.28, side: 1,
  name: none, ..s,
) = {
  let d = _sub(b, a)
  let len = _len(d)
  let u = _unit(d)
  let n = _scale(_perp(u), side)
  let h = _unit(_add(u, n))
  let main = draw.line(a, b, name: name, ..s)
  let hatches = ()
  for i in range(calc.floor(len / gap) + 1) {
    let p = _add(a, _scale(u, i * gap))
    hatches.push(draw.line(p, _add(p, _scale(h, hatch)), ..s))
  }
  main + hatches.join()
}

#let vector(a, b, name: none, ..s) = {
  draw.line(a, b, mark: (end: ">"), name: name, ..s)
}

#let spring(
  start, end,
  kind: "coil",
  amplitude: 0.25,
  segments: 10,
  name: none, ..s,
) = {
  let path = draw.line(start, end, ..s)
  if kind == "coil" {
    decorations.coil(path, amplitude: amplitude, segments: segments, name: name)
  } else if kind == "wave" {
    decorations.wave(path, amplitude: amplitude, segments: segments, name: name)
  } else if kind == "zigzag" {
    decorations.zigzag(path, amplitude: amplitude, segments: segments, name: name)
  } else {
    panic("spring: unknown kind `" + kind + "`")
  }
}

// ---------- Composite elements ----------

#let pendulum(pos, len: 1, angle: 30deg, r: 0.2, name: none, ..s) = {
  let rad = angle * calc.pi / 180
  let end = _add(pos, (len * calc.sin(rad), -len * calc.cos(rad)))
  pivot(pos).draw
  rod(pos, end, stroke: (thickness: 1.4pt, paint: gray))
  let bob = ball(end, r: r, name: name, ..s)
  bob.draw
  bob
}
