#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/lovelace:0.3.1": *

#set page(width: auto, height: auto)

#let t = sym.triangle.stroked.r

#let ass_2 = rule(
  label: [ass],
  rule(
    label: [var],
    [],
    $ "m'" =>^(M_5) S[S[S[0[]]]] $,
  ),
  $ M_6 #t "result" := "m'" #t M_7 $,
)

#let ass_3 = rule(
  label: [ass],
  rule(
    label: [cons],
    [],
    $ 0 [] =>^(M_3) 0 [] $,
  ),
  $ M_3 #t x := 0 [] #t M_4 $,
)

#let ass_4 = rule(
  label: [ass],
  rule(
    label: [cons],
    rule(
      label: [var],
      [],
      $ "m'" =>^(M_4) S[S[0[]]] $,
    ),
    $ S ["m'"] =>^(M_4) S[S[S[0[]]]] $,
  ),
  rule(
    label: [var],
    [],
    $ x =>^(M_4) 0 [] $,
  ),
  $ M_4 #t "m'", "n'" := S["m'"], x #t M_5 $,
)

#let sec_2 = rule(
  label: [sec],
  ass_3,
  ass_4,
  $ M_3 #t x := 0 []" ; ""m'", "n'" := S["m'"], x #t M_5 $,
)

#let loc_2 = rule(
  label: [local],
  sec_2,
  $ M_2 #t "local x" { x := 0 []" ; ""m'", "n'" := S["m'"], x } #t M_6 $,
)

#let while_2 = rule(
  label: [while-i],
  rule(
    label: [var],
    [],
    $ "n'" =>^(M_5) 0 [] $,
  ),
  $ M_6 #t "while n' is" { S" "[x] -> "m'", "n'" := S["m'"], x } #t M_6 $,
)

#let while_1 = rule(
  label: [while-ii],
  rule(
    label: [var],
    [],
    $ "n'" =>^(M_2) S[0[]] $,
  ),
  loc_2,
  while_2,
  $ M_2 #t "while n' is" { S" "[x] -> "m'", "n'" := S["m'"], x } #t M_6 $,
)

#let sec_1 = rule(
  label: [sec],
  while_1,
  ass_2,
  $ M_2 #t "while n' is {...}"" ; ""result" := "m'" #t M_7 $,
)

#let ass_1 = rule(
  label: [ass],
  rule(
    label: [var],
    [],
    $ m =>^(M_1) S [S [0 []]] $,
  ),
  rule(
    label: [var],
    [],
    $ n =>^(M_1) S [0 []] $,
  ),
  $ M_1 #t "m'", "n'" := "m", "n" #t M_2 $,
)

#let loc_1 = rule(
  label: [sec],
  ass_1,
  sec_1,
  $ M_1 #t "m'", "n'" := "m", "n"" ; ""while n' is {...}"" ; ""result" := "m'" #t M_7 $,
)

#let tree = rule(
  label: [loc],
  loc_1,
  $ M_0 #t "sumaP" #t M_8 $,
)

#prooftree(tree)

#v(1em)

#grid(columns: 2, column-gutter: 5em)[
  $
    & M_0 = (m, S[S[0[]]]), (n, S[0[]]) \
    & M_1 = ("m'", "null"), ("n'", "null"), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_2 = ("m'", S[S[0[]]]), ("n'", S[0[]]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_3 = (x, "null"), ("m'", S[S[0[]]]), ("n'", S[0[]]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_4 = (x, 0 []), ("m'", S[S[0[]]]), ("n'", S[0[]]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_5 = (x, 0 []), ("m'", S[S[S[0[]]]]), ("n'", 0[]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_6 = ("m'", S[S[S[0[]]]]), ("n'", 0[]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_7 = ("result", S[S[S[0[]]]]), ("m'", S[S[S[0[]]]]), ("n'", 0[]), (m, S[S[0[]]]), (n, S[0[]]) \
    & M_8 = ("result", S[S[S[0[]]]]), (m, S[S[0[]]]), (n, S[0[]]) \
  $
][
  // sumaP =
  // local m' n' {
  //    m', n' := m, n;
  //    while n' is {
  //       S [x] -> m', n' := S [m], x
  //    };
  //    result := m'
  // }

  sumaP =
  #box(baseline: (at: top, shift: -1.4em))[
    #pseudocode-list[
      - *local* m', n' {
        - m', n' := m, n ;
        - *while* n' *is* {
          - S [x] $->$ m', n' := S [m], x
        - } ;
        - result := m'
      - }
    ]
  ]
]
