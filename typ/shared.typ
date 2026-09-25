#import "@preview/noteworthy:0.4.0": *

// Typst's built-in title() renders document.title.
// Capture it here before the tylenotes parameter of the same name shadows it.
#let _document-title = title

// Whether the site generator (Calepin) is compiling this note for the web.
// Direct Typst compilation omits this key from sys.inputs, so this returns false
// and notes can always be compiled independently of the website.
#let is-web() = sys.inputs.at("calepin-target", default: "") == "html"

#let tylenotes(
  title : str,
  date : str,
  tags : (),
  summary : none,
  body,
) = {
  // Website metadata: read only by Calepin; invisible during ordinary compilation.
  let meta = (title: title, date: date, tags: tags)
  if summary != none { meta.insert("summary", summary) }
  [#metadata(meta) <website-metadata>]

  // Render the H1 explicitly for the web: noteworthy's title appears only in
  // paged output and is omitted from HTML exports. In paged output, calling
  // title() again would add a whole extra page, so guard it with this condition.
  set document(title: title)
  if is-web() { _document-title() }

  noteworthy.with(
    title: title,
    author: "zzj",
    date: date,
  )(body)
}

// Equation numbering, for notes compiled to both PDF and the website.
//
// Typst's HTML export drops the number of a numbered equation: `numbering` is
// ignored silently — no warning in the build log, no `(1)` on the page — while
// `@eq:` references keep resolving, so a note reaches the web looking merely
// unfinished.
//
// `equations` is the site's own numbering, and the one notes should use:
//
//   #show: equations                            // (1), (2), ...
//   #show: equations.with(numbering: "(a)")     // (a), (b), ...
//   #show: equations.with(number-align: left)   // numbers on the left
//
// Paged output keeps Typst's native numbering; HTML gets the number beside the
// untouched formula, which also keeps the equation's label — and therefore
// `@eq:` — exactly where the note put it. References print the bare number,
// `(1)` rather than `Equation 1`, in both outputs.
//
// It lives here, next to `tylenotes`, for the same reason: every note imports
// this file, so one line in the note works whether the note is compiled on its
// own or published. The website's theme imports these names from here — it owns
// only the HTML the number is drawn into, since `html.elem` is how the web gets
// a box beside the formula that HTML export cannot place itself.
#let _numbering = numbering
#let _site-equations = state("site/equations", false)

#let _site-note-equation(it) = {
  // `align`, `grid` and `place` are all ignored — and emptied — during HTML
  // export, so the two boxes are placed by CSS instead of by a layout element.
  // A multi-line equation keeps its `&` alignment as one MathML table and is
  // numbered as a whole: HTML cannot put a number on one line of it.
  let edge = if it.number-align in (left, start) { "start" } else { "end" }
  let number = context counter(math.equation).display(it.numbering)
  html.elem("div", attrs: (class: "note-equation note-equation-" + edge), {
    html.elem("div", attrs: (class: "note-equation-body"), it)
    html.elem("div", attrs: (class: "note-equation-number"), number)
  })
}

#let _site-equation-ref(it) = {
  if it.element == none or it.element.func() != math.equation { return it }
  if it.element.numbering == none { return it }
  let target = it.element
  let loc = target.location()
  context link(loc, _numbering(target.numbering, ..counter(math.equation).at(loc)))
}

#let equations(numbering: "(1)", number-align: right, body) = {
  set math.equation(numbering: numbering, number-align: number-align)
  show ref: _site-equation-ref
  show math.equation.where(block: true): it => {
    // An environment may replace the numbering inside its own body — `theoretic`
    // marks the equation ending a proof with a `numbering` function that draws
    // the QED box and steps the counter back — and those equations keep whatever
    // the native export already does with them.
    if is-web() and it.numbering == numbering { _site-note-equation(it) } else { it }
  }
  _site-equations.update(true)
  body
}

// A note that numbers equations with a plain `#set math.equation(numbering: ...)`
// is still numbered by this hook, which `scripts/sync-notes.sh` gives every
// synchronized copy. It cannot see a set rule a note wrote for itself, so it
// numbers whatever the equation claims, and stands down while `equations` is in
// charge — hence `_site-equations`. Paged output passes through untouched.
#let web-equations(body) = {
  if not is-web() { return body }
  show math.equation: it => context {
    // Only a counting number is rebuilt here: a function `numbering` belongs to
    // the environment that set it, not to the note.
    if not it.block or type(it.numbering) != str { return it }
    if _site-equations.get() { return it }
    _site-note-equation(it)
  }
  body
}
