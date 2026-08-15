#import "@preview/noteworthy:0.4.0": *

#let tylenotes(
  title : str,
  date : str,
  body,
) = {
  noteworthy.with(
    title: title,
    author: "zzj",
    date: date,
  )(body) 
}

