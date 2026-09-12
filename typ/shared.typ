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
