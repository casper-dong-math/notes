#let abbrev = (
  def: "Definition",
  lem: "Lemma",
  thm: "Theorem",
  cor: "Corollary",
  prop: "Proposition",
)

#let state(type: "thm", title: none, body) = {
  let line=[#text(weight: "bold")[#abbrev.at(type)]]
  if title != none {
    line += [ (#text(style: "italic")[#title])]
  }
  block(
    fill: luma(250),
    stroke: 1pt + black,
    inset: 1em,
    width: 100%,
    radius: 5pt,
    below: 1em,
    line + [\ #body],
  )
}

#let sketch(body) = block(
  //fill: luma(240),
  stroke: (left: 3pt + luma(88)), 
  inset: (left: 1em, top: 0.5em, bottom: 0.5em),
  width: 100%,
  below: 1em,
)[
  *Sketch of proof* \
  #body
]

#let remark(body) = block(
  //fill: aqua.lighten(80%),
  stroke: (left: 3pt + eastern), 
  inset: (left: 1em, top: 0.5em, bottom: 0.5em),
  width: 100%,
  below: 1em,
)[
  #text(fill: eastern)[*Remark:*] #body
]

#let intuit(body) = block(
  //fill: lime.lighten(88%),
  stroke: (left: 3pt + green), 
  inset: (left: 1em, top: 0.5em, bottom: 0.5em),
  width: 100%,
  below: 1em,
)[
  #text(fill:green)[*Intuition:*] #body
]

#let alert(body) = block(
  //fill: red.lighten(90%),
  stroke: (left: 3pt + red),
  inset: (left: 1em, top: 0.5em, bottom: 0.5em),
  width: 100%,
  below: 1em,
)[
   #text(fill: red)[*Warning:*] #body
]
