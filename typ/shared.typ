#import "@preview/noteworthy:0.4.0": *

// Typst 内置的 title()：渲染 document.title。
// tylenotes 有个同名参数会遮蔽它，所以先在这里捕获一份。
#let _document-title = title

// 当前是否正在被网站生成器（Calepin）编译成网页。
// 直接用 typst 编译时 sys.inputs 里没有这个键，于是返回 false，
// 所以笔记始终可以脱离网站单独编译。
#let is-web() = sys.inputs.at("calepin-target", default: "") == "html"

#let tylenotes(
  title : str,
  date : str,
  tags : (),
  summary : none,
  body,
) = {
  // 网站元数据：只有 Calepin 会读取；普通编译时它只是一个不可见元素。
  let meta = (title: title, date: date, tags: tags)
  if summary != none { meta.insert("summary", summary) }
  [#metadata(meta) <website-metadata>]

  // 网页版需要自己排 H1：noteworthy 的标题只出现在分页输出里，HTML 导出会丢掉。
  // 分页版由 noteworthy 排标题，这里再调一次 title() 会多出一整页，所以必须判断。
  set document(title: title)
  if is-web() { _document-title() }

  noteworthy.with(
    title: title,
    author: "zzj",
    date: date,
  )(body)
}
